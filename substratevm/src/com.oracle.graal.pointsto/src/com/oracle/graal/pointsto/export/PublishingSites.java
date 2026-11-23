/*
 * Copyright (c) 2026, 2026, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */
package com.oracle.graal.pointsto.export;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.regex.Pattern;

import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.export.FlowReader.Held;
import com.oracle.graal.pointsto.export.ThreadEscape.Described;
import com.oracle.graal.pointsto.export.ThreadEscape.OpaqueCall;
import com.oracle.graal.pointsto.export.ThreadEscape.UnsafeStore;
import com.oracle.graal.pointsto.flow.ArrayCopyTypeFlow;
import com.oracle.graal.pointsto.flow.CallSiteSensitiveMethodTypeFlow;
import com.oracle.graal.pointsto.flow.CloneTypeFlow;
import com.oracle.graal.pointsto.flow.InvokeTypeFlow;
import com.oracle.graal.pointsto.flow.MethodFlowsGraph;
import com.oracle.graal.pointsto.flow.OffsetStoreTypeFlow;
import com.oracle.graal.pointsto.flow.StoreFieldTypeFlow;
import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.flow.context.object.AnalysisObject;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisMethod;

/**
 * The places where a reference moves into another object or leaves the analyzed code: field and
 * array stores, unsafe and VarHandle stores, array copies, clones, and calls. A store, copy or
 * clone becomes a site that shares what it moves once a target object has shared contents. A call
 * either shares its arguments, links them (see {@link ThreadEscape}), or does nothing, depending on
 * what the facts say about its callees.
 */
final class PublishingSites {

    private enum Kind {
        /** Shares what it stores. */
        STORE,
        /** Shares the contents of the source it copies from. */
        COPY,
        /** Shares the contents of the cloned objects of the same exact type. */
        CLONE
    }

    /** A store, copy or clone into objects: once a target's contents are shared, what goes into it is shared. */
    static final class Site {
        final Kind kind;
        final Supplier<String> what;
        final Held value;
        /** The field stored into, if any. */
        final AnalysisField field;
        /** The flows the value comes from, for explanations. */
        List<TypeFlow<?>> flows = List.of();
        boolean fired;

        Site(Kind kind, Supplier<String> what, Held value, AnalysisField field) {
            this.kind = kind;
            this.what = what;
            this.value = value;
            this.field = field;
        }
    }

    /** Deferred until all stores are known: if the target is a saturated flow's, its objects are resolved from the stores into what it loads. */
    record PendingSite(Site site, Held target) {
    }

    /**
     * A call to a method with an unknown effect, as the objects passed to it: per object argument,
     * the objects the analysis knows it may be, or the declared type if its flow saturated.
     */
    private static final class Call {
        final String callee;
        final List<Held> arguments = new ArrayList<>();
        /** Whether this argument's objects were already shared because another argument was. */
        final List<Boolean> spread = new ArrayList<>();

        Call(String callee) {
            this.callee = callee;
        }
    }

    /** An object passed to a linking call, at an argument position. */
    record Link(Call call, int position) {
    }

    /** Natives of Object and Class that store no reference (see {@link #isPure}). */
    private static final Set<String> PURE_OBJECT = Set.of("getClass", "hashCode", "notify", "notifyAll", "wait0", "wait");
    private static final Set<String> PURE_CLASS = Set.of("isInstance", "isAssignableFrom", "isInterface", "isArray", "isPrimitive", "isHidden", "isRecord", "isAnnotation", "isEnum", "getModifiers",
                    "getSuperclass", "getComponentType", "getName", "desiredAssertionStatus");

    // Shared with the thread-escape run these sites belong to.
    private final ThreadEscape escape;
    private final PointsToAnalysis bb;
    private final AnalysisUniverse universe;
    private final boolean readFlows;
    private final AnalysisType objectType;
    private final Pattern explain;
    private final Map<AnalysisType, List<AnalysisObject>> uncontained;
    private final List<Runnable> afterCollection;
    FlowReader reader;
    StoredPlaces places;
    SharingExplanation why;

    /** How completely the facts describe each method. */
    final Function<AnalysisMethod, Described> described;

    /** Whether the graphs will be compiled, so a call without targets can never execute. */
    final boolean compiled;

    /** What the export found that the flows don't show: unmodeled stores and calls into unseen code. */
    final List<UnsafeStore> unsafeStores;
    final List<OpaqueCall> opaqueCalls;

    /** Sites created but not yet attached to their target objects (see {@link #register}). */
    final List<PendingSite> pendingSites = new ArrayList<>();

    /** Sites by the objects they may store into. */
    final Map<AnalysisObject, List<Site>> sitesByObject = new HashMap<>();

    /** Sites whose target flow saturated, by the type of objects they may store into. */
    final Map<AnalysisType, List<Site>> sitesByType = new HashMap<>();

    /** Linking calls, by the objects passed to them and by the types of saturated arguments. */
    final Map<AnalysisObject, List<Link>> links = new HashMap<>();
    final Map<AnalysisType, List<Link>> linksByType = new HashMap<>();

    // Counts for the diagnostics.
    int storeSites;
    int copySites;
    int linkedCalls;

    PublishingSites(ThreadEscape escape, Function<AnalysisMethod, Described> described, boolean compiled, List<UnsafeStore> unsafeStores, List<OpaqueCall> opaqueCalls) {
        this.escape = escape;
        this.bb = escape.bb;
        this.universe = escape.universe;
        this.readFlows = escape.readFlows;
        this.objectType = escape.objectType;
        this.explain = escape.explain;
        this.uncontained = escape.uncontained;
        this.afterCollection = escape.afterCollection;
        this.described = described;
        this.compiled = compiled;
        this.unsafeStores = unsafeStores;
        this.opaqueCalls = opaqueCalls;
    }

    /** Connects the sites to the other parts of thread escape, created after them. */
    void connect(FlowReader reader, StoredPlaces places, SharingExplanation why) {
        this.reader = reader;
        this.places = places;
        this.why = why;
    }

    /** The sites for a flow: a store, an array copy or a clone. What it stores is shared once a target's contents are. */
    void sites(AnalysisMethod method, TypeFlow<?> flow) {
        if (escape.inVirtualMachine(method)) {
            // Under vm-code, VM code stores only where VM code reads, except into JDK and program objects, which others read.
            AnalysisField stored = flow instanceof StoreFieldTypeFlow store ? store.field() : null;
            if (stored == null || stored.getDeclaringClass().toJavaName(true).startsWith(ThreadEscape.VM)) {
                return;
            }
        }
        if (flow instanceof StoreFieldTypeFlow.StoreStaticFieldTypeFlow store) {
            // Every thread can reach a static field.
            if (store.valueFlow() != null && !escape.isPrivate(store.field()) && !ThreadEscape.LEAVE_OUT.contains("static")) {
                afterCollection.add(() -> shareStaticStore(method, store));
                storeSites++;
            }
        } else if (flow instanceof StoreFieldTypeFlow.StoreInstanceFieldTypeFlow store && store.valueFlow() != null && !escape.isPrivate(store.field()) && !ThreadEscape.LEAVE_OUT.contains("field")) {
            site(Kind.STORE, () -> "a store into " + store.field().format("%H.%n") + " in " + method.format("%H.%n"), reader.observedBy(store, store.receiver()), store.valueFlow(), store.field());
        } else if (flow instanceof OffsetStoreTypeFlow store && store.valueFlow() != null && !isStoreApi(method) && !ThreadEscape.LEAVE_OUT.contains("array")) {
            boolean indexed = store instanceof OffsetStoreTypeFlow.StoreIndexedTypeFlow;
            site(Kind.STORE, () -> "a " + (indexed ? "store into an array" : "unsafe store") + " in " + method.format("%H.%n"), reader.held(reader.observedBy(store, store.receiver()), true), reader
                            .held(store.valueFlow(), true), null,
                            List.of(store.valueFlow()), !indexed, true);
            if (!indexed && !readFlows && !bb.analysisPolicy().useConservativeUnsafeAccess() && !universe.getUnsafeAccessedStaticFields().isEmpty()) {
                unsafeStoreIntoStatics(method, store);
            }
        } else if (flow instanceof ArrayCopyTypeFlow copy && !ThreadEscape.LEAVE_OUT.contains("copy")) {
            site(Kind.COPY, () -> "a copy between arrays in " + method.format("%H.%n"), copy.destination(), copy.source(), null);
        } else if (flow instanceof CloneTypeFlow clone && bb.analysisPolicy().allocationSiteSensitiveHeap()) {
            // Without allocation sites, a clone is the same abstract object as its original and shares its flows.
            site(Kind.CLONE, () -> "a clone in " + method.format("%H.%n"), clone, reader.observedBy(clone, clone.input()), null);
        }
    }

    /** A static store shares what it stores, since every thread can reach it. */
    private void shareStaticStore(AnalysisMethod method, StoreFieldTypeFlow.StoreStaticFieldTypeFlow store) {
        why.because(() -> "a store into the static field " + store.field().format("%H.%n") + " in " + method.format("%H.%n"), null);
        Held stored = reader.held(store.valueFlow(), true);
        if (explain != null && explain.matcher(store.field().format("%H.%n")).find()) {
            PointsToExport.diagnostics().println("THREADESCAPE a store into the static field " + store.field().format("%H.%n") + " shares " + why.describe(stored) + " " + why.summary(stored));
            for (FlowReader.Source source : stored.stored()) {
                if (source.key() instanceof TypeFlow<?> saturated) {
                    Held rebuilt = reader.rebuild(saturated);
                    PointsToExport.diagnostics().println("THREADESCAPE   the saturated " + GraphExport.simpleClassName(saturated) + " of declared type " + saturated.getDeclaredType() +
                                    " (filters " + source.filters() + ") is rebuilt as " +
                                    why.describe(rebuilt) + " " + why.summary(rebuilt));
                }
            }
        }
        escape.share(stored);
    }

    /**
     * The analysis lets an unsafe store write a static field whatever its target; the base of such a
     * store is the array holding the statics. A store whose base may be that array shares what it
     * stores.
     */
    private void unsafeStoreIntoStatics(AnalysisMethod method, OffsetStoreTypeFlow store) {
        Held base = reader.held(reader.observedBy(store, store.receiver()), true);
        if (base.isNothing() || !base.any().isEmpty() || FlowReader.hasArray(base.objectsIn(bb))) {
            afterCollection.add(() -> {
                why.because(() -> "an unsafe store in " + method.format("%H.%n") + ", which may write a static field", null);
                escape.share(reader.held(store.valueFlow(), true));
            });
        }
    }

    private void site(Kind kind, Supplier<String> what, TypeFlow<?> into, TypeFlow<?> value, AnalysisField field) {
        site(kind, what, reader.held(into, true), reader.held(value, true), field, List.of(value), false, true);
    }

    /**
     * Creates a site for a store, copy or clone, and records the stored value under its target place
     * for saturated loads that read from there.
     *
     * @param unsafe whether it is an unsafe or VarHandle store, which may target a field
     * @param array whether it certainly targets an array; otherwise whether it may
     */
    private void site(Kind kind, Supplier<String> what, Held target, Held stored, AnalysisField field, List<TypeFlow<?>> flows, boolean unsafe, boolean array) {
        boolean isArrayStore = array && (!unsafe || reader.mayBeArray(target));
        if (target.isNothing() || stored.isNothing()) {
            return;
        }
        Site site = new Site(kind, what, stored, field);
        if (kind == Kind.STORE) {
            if (field != null) {
                places.storedInField.computeIfAbsent(field, k -> new ArrayList<>()).add(stored);
            } else if (isArrayStore) {
                places.storedInArrays.add(stored);
                if (explain != null && (!stored.any().isEmpty() || !stored.stored().isEmpty())) {
                    why.arrayStoresOfAny.add(what.get() + "  stores " + why.summary(stored));
                }
            }
            if (field == null && (!isArrayStore || unsafe)) {
                // It may target a field accessed through unsafe.
                places.storedUnsafely.add(stored);
            }
        }
        if (explain != null) {
            site.flows = flows;
            if (explain.matcher(what.get()).find()) {
                PointsToExport.diagnostics().println("THREADESCAPE site (" + kind + ") " + what.get() + "\n    into " + why.describe(target) + " " + why.summary(target) + "\n    value " + why
                                .describe(stored) + " " + why.summary(stored));
            }
        }
        if (kind == Kind.STORE) {
            storeSites++;
        } else {
            copySites++;
        }
        pendingSites.add(new PendingSite(site, target));
    }

    /** Attaches a site to its target objects, once all stores (and so all saturated targets) are known. */
    void register(Site site, Held rawTarget) {
        Held target = places.expand(rawTarget);
        if (explain != null && explain.matcher(site.what.get()).find()) {
            int count = 0;
            StringBuilder names = new StringBuilder();
            for (AnalysisObject object : target.objectsIn(bb)) {
                if (count++ < 6) {
                    names.append(GraphExport.PointsTo.objectName(object)).append("; ");
                }
            }
            PointsToExport.diagnostics().println("THREADESCAPE registered " + site.what.get() + " into " + count + " objects: " + names + " any " + target.any().stream().map(AnalysisType::toJavaName)
                            .toList() + " from " + why.summary(rawTarget));
        }
        for (AnalysisObject object : target.objectsIn(bb)) {
            if (site.kind != Kind.CLONE && object.isEmptyObjectArrayConstant(bb)) {
                // Nothing can be stored into an array type without elements.
                continue;
            }
            sitesByObject.computeIfAbsent(object, k -> new ArrayList<>(2)).add(site);
        }
        for (AnalysisType type : target.any()) {
            sitesByType.computeIfAbsent(type, k -> new ArrayList<>(2)).add(site);
        }
    }

    /** An unmodeled store: a site on its target objects, or, if the target is unknown, a store into anything. */
    void unsafeStore(UnsafeStore store) {
        if (escape.inVirtualMachine(store.method()) || isStoreApi(store.method())) {
            return;
        }
        Held stored = store.value() == null ? new Held(List.of(), List.of(store.valueType() != null ? store.valueType() : objectType)) : heldOf(store.method(), store.value());
        if (stored.isNothing()) {
            return;
        }
        if (store.base() == null) {
            afterCollection.add(() -> {
                why.because(() -> "an unsafe store in " + store.where() + " into something the analysis can't name", null);
                escape.share(stored);
            });
            places.storedInArrays.add(stored);
            places.storedUnsafely.add(stored);
            storeSites++;
        } else {
            site(Kind.STORE, () -> "an unsafe store in " + store.where(), heldOf(store.method(), store.base()), stored, null, store.value() == null ? List.of() : store.value(), true, true);
        }
    }

    /** What a method's flows may hold, over every context the method was analyzed in. */
    Held heldOf(PointsToAnalysisMethod method, List<TypeFlow<?>> originals) {
        Held held = Held.NOTHING;
        for (TypeFlow<?> original : originals) {
            if (method.getTypeFlow() instanceof CallSiteSensitiveMethodTypeFlow sensitive) {
                for (MethodFlowsGraph clone : sensitive.getFlows()) {
                    held = held.with(reader.held(clone.lookupCloneOf(bb, original), true));
                }
            } else {
                held = held.with(reader.held(original, true));
            }
        }
        return held;
    }

    /**
     * What a call does with its arguments, from the facts about its callees. A method without facts
     * may share them and its result; a method with an unknown effect links its arguments.
     */
    void call(AnalysisMethod caller, InvokeTypeFlow invoke) {
        Collection<AnalysisMethod> callees = invoke.getOriginalCallees();
        if (callees.stream().anyMatch(PublishingSites::isStoreApi) && !escape.inVirtualMachine(caller) && !isStoreApi(caller) && !ThreadEscape.LEAVE_OUT.contains("handle")) {
            storeApi(caller, invoke);
        }
        AnalysisMethod nothing = null;
        AnalysisMethod unknown = null;
        for (AnalysisMethod callee : callees) {
            if (isStoreApi(callee) || isPure(callee)) {
                // Its effects are known: it stores where its arguments say, or nowhere.
                continue;
            }
            switch (described.apply(callee)) {
                case NOTHING -> nothing = nothing == null ? callee : nothing;
                case UNKNOWN_EFFECT -> unknown = unknown == null ? callee : unknown;
                case WHOLE -> {
                }
            }
        }
        if (nothing != null || (callees.isEmpty() && !compiled)) {
            AnalysisMethod culprit = nothing;
            afterCollection.add(() -> shareOpaqueCall(caller, invoke, culprit));
        } else if (unknown != null && !escape.inVirtualMachine(caller)) {
            AnalysisMethod culprit = unknown;
            afterCollection.add(() -> linkCall(caller, invoke, culprit));
        }
    }

    /** A call to a method without facts: its arguments and result are shared. */
    private void shareOpaqueCall(AnalysisMethod caller, InvokeTypeFlow invoke, AnalysisMethod culprit) {
        for (TypeFlow<?> argument : invoke.getActualParameters()) {
            if (argument != null) {
                why.because(() -> "argument of a call in " + caller.format("%H.%n") + " to " + opaqueCallee(culprit) + (argument.isSaturated() ? " (saturated flow)" : ""), null);
                escape.share(reader.held(argument, true));
            }
        }
        if (invoke.getActualReturn() != null) {
            why.because(() -> "result of a call in " + caller.format("%H.%n") + " to " + opaqueCallee(culprit), null);
            escape.share(reader.held(invoke.getActualReturn(), true));
        }
    }

    /** The callee of a call to a method without facts, for explanations. */
    private static String opaqueCallee(AnalysisMethod culprit) {
        return culprit == null ? "a method without targets" : culprit.format("%H.%n") + ", which the facts don't have";
    }

    /** A call to a method with an unknown effect: its arguments are linked. */
    private void linkCall(AnalysisMethod caller, InvokeTypeFlow invoke, AnalysisMethod unknown) {
        Call call = new Call(unknown.format("%H.%n") + " in " + caller.format("%H.%n"));
        for (TypeFlow<?> argument : invoke.getActualParameters()) {
            if (argument == null || argument.isPrimitiveFlow()) {
                continue;
            }
            Held passed = places.expand(reader.held(argument, true));
            if (!passed.isNothing()) {
                call.arguments.add(passed);
                call.spread.add(false);
            }
        }
        if (call.arguments.size() < 2) {
            return;
        }
        linkedCalls++;
        for (int position = 0; position < call.arguments.size(); position++) {
            Link link = new Link(call, position);
            Held passed = call.arguments.get(position);
            for (AnalysisObject object : passed.objectsIn(bb)) {
                links.computeIfAbsent(object, k -> new ArrayList<>(2)).add(link);
            }
            for (AnalysisType type : passed.any()) {
                linksByType.computeIfAbsent(type, k -> new ArrayList<>(2)).add(link);
            }
        }
    }

    /**
     * Whether a method stores a reference at an offset into its argument, like the unsafe and
     * VarHandle accessors. Their one body serves every field and object, so its flows merge all
     * calls; each call's own arguments say exactly what goes where.
     */
    private static boolean isStoreApi(AnalysisMethod method) {
        String owner = method.getDeclaringClass().toJavaName(true);
        String name = method.getName();
        if (owner.equals("jdk.internal.misc.Unsafe")) {
            return name.contains("Reference") && (name.startsWith("put") || name.contains("compareAnd") || name.contains("weakCompareAnd") || name.startsWith("getAndSet"));
        }
        return owner.startsWith("java.lang.invoke.VarHandleReferences$") && (name.startsWith("set") || name.contains("compareAnd") || name.contains("weakCompareAnd") || name.startsWith("getAndSet"));
    }

    /**
     * Whether a method without facts stores no reference and returns none it wasn't given: the
     * natives of Object and Class that read an object or its class, and the identity hash code. The
     * language fixes their behavior.
     */
    private static boolean isPure(AnalysisMethod method) {
        String owner = method.getDeclaringClass().toJavaName(true);
        String name = method.getName();
        return owner.equals("java.lang.Object") && PURE_OBJECT.contains(name) || owner.equals("java.lang.Class") && PURE_CLASS.contains(name) ||
                        owner.equals("java.lang.System") && name.equals("identityHashCode");
    }

    /**
     * A call to a store accessor stores its last object argument into its first one (after the
     * accessor's own receiver, the handle or the Unsafe object). With only one object argument it is a
     * static store, which every thread can reach.
     */
    private void storeApi(AnalysisMethod caller, InvokeTypeFlow invoke) {
        List<TypeFlow<?>> objects = new ArrayList<>();
        TypeFlow<?>[] arguments = invoke.getActualParameters();
        for (int i = 1; i < arguments.length; i++) {
            if (arguments[i] != null && !arguments[i].isPrimitiveFlow()) {
                objects.add(arguments[i]);
            }
        }
        if (objects.size() == 1) {
            afterCollection.add(() -> {
                why.because(() -> "a store into a static field through a handle or unsafe, in " + caller.format("%H.%n"), null);
                escape.share(reader.held(objects.get(0), true));
            });
            storeSites++;
        } else if (objects.size() >= 2) {
            site(Kind.STORE, () -> "a store through a handle or unsafe in " + caller.format("%H.%n"), reader.held(objects.get(0), true), reader.held(objects.get(objects.size() - 1), true), null,
                            List.of(objects.get(objects.size() - 1)), true, true);
        }
    }

    /** A target's contents became shared: share what the site stores, or the contents of what it copies from. */
    void fire(Site site, AnalysisObject object) {
        switch (site.kind) {
            case STORE -> {
                if (!site.fired) {
                    site.fired = true;
                    why.because(() -> site.what.get() + ", and the contents of " + GraphExport.PointsTo.objectName(object) + " are shared; it stores " + why.summary(site.value), object, site.flows);
                    escape.share(site.value);
                }
            }
            case COPY -> {
                if (!site.fired) {
                    site.fired = true;
                    why.because(() -> site.what.get() + ", and the contents of " + GraphExport.PointsTo.objectName(object) + " are shared", object);
                    escape.shareContents(site.value);
                }
            }
            case CLONE -> {
                // A clone has the type of the original.
                AnalysisType type = object.type();
                why.because(() -> site.what.get() + ", and the contents of " + GraphExport.PointsTo.objectName(object) + " are shared", object);
                Held cloning = places.expand(site.value);
                for (AnalysisObject cloned : cloning.objectsIn(bb)) {
                    if (cloned.type().equals(type)) {
                        escape.shareContents(cloned);
                    }
                }
                for (AnalysisType cloned : cloning.any()) {
                    if (cloned.isAssignableFrom(type)) {
                        List<AnalysisObject> same = uncontained.remove(type);
                        if (same != null) {
                            same.forEach(escape::shareContents);
                        }
                        escape.shareContents(type.getContextInsensitiveAnalysisObject());
                    }
                }
            }
        }
    }

    /** An object passed to a linking call became shared: share the call's other arguments, once each. */
    void spread(Link link, AnalysisObject object) {
        Call call = link.call();
        for (int other = 0; other < call.arguments.size(); other++) {
            if (other != link.position() && !call.spread.get(other)) {
                call.spread.set(other, true);
                why.because(() -> "an argument of a call to " + call.callee + ", which may copy references between its arguments, with " + GraphExport.PointsTo.objectName(object), object);
                escape.share(call.arguments.get(other));
            }
        }
    }
}
