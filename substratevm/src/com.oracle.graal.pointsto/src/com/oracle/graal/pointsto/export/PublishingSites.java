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
import com.oracle.graal.pointsto.export.FlowReader.StreamSupportHelper;
import com.oracle.graal.pointsto.export.ThreadEscape.Described;
import com.oracle.graal.pointsto.export.ThreadEscape.OpaqueCall;
import com.oracle.graal.pointsto.export.ThreadEscape.UnsafeStore;
import com.oracle.graal.pointsto.flow.ArrayCopyTypeFlow;
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
 * The places in the program where a reference moves from one object to another or leaves the analyzed
 * code: stores into fields and arrays, unsafe and handle stores, copies between arrays, clones, and calls.
 * A store, copy or clone becomes a site, which shares what it moves once an object it may move it into has
 * shared contents. A call is described by what the facts say of its callees: it shares its arguments, or
 * links the objects of its arguments, or does nothing.
 */
final class PublishingSites {

    private enum Kind {
        /** Shares what it stores. */
        STORE,
        /** Shares the contents of what it copies from. */
        COPY,
        /** Shares the contents of the objects of the same exact type that it clones. */
        CLONE
    }

    /**
     * Something stored, or copied, into objects: once the contents of an object it may go into are
     * shared, what goes into it is.
     */
    static final class Site {
        final Kind kind;
        final Supplier<String> what;
        final Held value;
        /** The field stored into, if it is one. */
        final AnalysisField field;
        /** The flows the value comes from, kept to explain. */
        List<TypeFlow<?>> flows = List.of();
        boolean fired;

        Site(Kind kind, Supplier<String> what, Held value, AnalysisField field) {
            this.kind = kind;
            this.what = what;
            this.value = value;
            this.field = field;
        }
    }

    /**
     * What is done once every store is known: where a store goes into, when the object stored
     * into is a saturated flow's, is what the stores into what it loads from say.
     */
    record PendingSite(Site site, Held target) {
    }

    /**
     * A call to a method with an effect the facts can't name, as the objects passed to it: for each
     * argument that is an object, those the analysis knows it may be, or the declared type of a
     * saturated flow.
     */
    private static final class Call {
        final String callee;
        final List<Held> arguments = new ArrayList<>();
        /** Whether the objects of this argument were shared for another one being. */
        final List<Boolean> spread = new ArrayList<>();

        Call(String callee) {
            this.callee = callee;
        }
    }

    record Link(Call call, int position) {
    }

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

    final Function<AnalysisMethod, Described> described;

    /** Whether the graphs are about to be compiled, so that a call without targets never happens. */
    final boolean compiled;

    final List<UnsafeStore> unsafeStores;
    final List<OpaqueCall> opaqueCalls;
    final List<PendingSite> pendingSites = new ArrayList<>();
    final Map<AnalysisObject, List<Site>> sitesByObject = new HashMap<>();

    /** The sites that may go into any object of a type: their flow saturated. */
    final Map<AnalysisType, List<Site>> sitesByType = new HashMap<>();

    int storeSites;
    int copySites;
    final Map<AnalysisObject, List<Link>> links = new HashMap<>();
    final Map<AnalysisType, List<Link>> linksByType = new HashMap<>();
    int linkedCalls;
    private static final Set<String> PURE_OBJECT = Set.of("getClass", "hashCode", "notify", "notifyAll", "wait0", "wait");
    private static final Set<String> PURE_CLASS = Set.of("isInstance", "isAssignableFrom", "isInterface", "isArray", "isPrimitive", "isHidden", "isRecord", "isAnnotation", "isEnum", "getModifiers",
                    "getSuperclass", "getComponentType", "getName", "desiredAssertionStatus");

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

    void connect(FlowReader reader, StoredPlaces places, SharingExplanation why) {
        this.reader = reader;
        this.places = places;
        this.why = why;
    }

    /**
     * The sites a flow is: a store into an object, a copy between arrays, a clone. What the
     * flow stores is shared once the contents of an object it may be stored into are.
     */
    void sites(AnalysisMethod method, TypeFlow<?> flow) {
        if (escape.inVirtualMachine(method)) {
            // The virtual machine's code stores where it reads, but not into the objects of the JDK and the program that others read.
            AnalysisField stored = flow instanceof StoreFieldTypeFlow store ? store.field() : null;
            if (stored == null || stored.getDeclaringClass().toJavaName(true).startsWith(ThreadEscape.VM)) {
                return;
            }
        }
        if (flow instanceof StoreFieldTypeFlow.StoreStaticFieldTypeFlow store) {
            // Every thread reaches a static field.
            if (store.valueFlow() != null && !escape.isPrivate(store.field()) && !ThreadEscape.LEAVE_OUT.contains("static")) {
                afterCollection.add(() -> {
                    why.because(() -> "a store into the static field " + store.field().format("%H.%n") + " in " + method.format("%H.%n"), null);
                    escape.share(reader.held(store.valueFlow(), true));
                });
                storeSites++;
            }
        } else if (flow instanceof StoreFieldTypeFlow.StoreInstanceFieldTypeFlow store && store.valueFlow() != null && !escape.isPrivate(store.field()) && !ThreadEscape.LEAVE_OUT.contains("field")) {
            site(Kind.STORE, () -> "a store into " + store.field().format("%H.%n") + " in " + method.format("%H.%n"), reader.observedBy(store, store.receiver()), store.valueFlow(), store.field());
        } else if (flow instanceof OffsetStoreTypeFlow store && store.valueFlow() != null && !isStoreApi(method) && !ThreadEscape.LEAVE_OUT.contains("array")) {
            boolean indexed = store instanceof OffsetStoreTypeFlow.StoreIndexedTypeFlow;
            site(Kind.STORE, () -> "a " + (indexed ? "store into an array" : "unsafe store") + " in " + method.format("%H.%n"), reader.held(reader.observedBy(store, store.receiver()), true), reader.held(store.valueFlow(), true), null,
                            List.of(store.valueFlow()), !indexed, true);
            if (!(store instanceof OffsetStoreTypeFlow.StoreIndexedTypeFlow) && !readFlows && !bb.analysisPolicy().useConservativeUnsafeAccess() && !universe.getUnsafeAccessedStaticFields().isEmpty()) {
                // The analysis lets an unsafe store write a static field, whatever the object it stores into; its base is the array that holds statics.
                Held base = reader.held(reader.observedBy(store, store.receiver()), true);
                if (base.isNothing() || !base.any().isEmpty() || StreamSupportHelper.hasArray(base.objectsIn(bb))) {
                    afterCollection.add(() -> {
                        why.because(() -> "an unsafe store in " + method.format("%H.%n") + ", which may write a static field", null);
                        escape.share(reader.held(store.valueFlow(), true));
                    });
                }
            }
        } else if (flow instanceof ArrayCopyTypeFlow copy && !ThreadEscape.LEAVE_OUT.contains("copy")) {
            site(Kind.COPY, () -> "a copy between arrays in " + method.format("%H.%n"), copy.destination(), copy.source(), null);
        } else if (flow instanceof CloneTypeFlow clone && bb.analysisPolicy().allocationSiteSensitiveHeap()) {
            // Without allocation sites, a clone is the same abstract object as what it clones, and has its flows.
            site(Kind.CLONE, () -> "a clone in " + method.format("%H.%n"), clone, reader.observedBy(clone, clone.input()), null);
        }
    }

    private void site(Kind kind, Supplier<String> what, TypeFlow<?> into, TypeFlow<?> value, AnalysisField field) {
        site(kind, what, reader.held(into, true), reader.held(value, true), field, List.of(value), false, true);
    }

    /**
     * @param unsafe whether the store is an unsafe or a handle's, which may be into a field
     * @param array whether it is into an array for sure; otherwise whether it may be
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
            if (field == null && !isArrayStore || field == null && unsafe) {
                places.storedUnsafely.add(stored);
            }
        }
        if (explain != null) {
            site.flows = flows;
            if (explain.matcher(what.get()).find()) {
                System.err.println("THREADESCAPE site (" + kind + ") " + what.get() + "\n    into " + why.describe(target) + " " + why.summary(target) + "\n    value " + why.describe(stored) + " " + why.summary(stored));
            }
        }
        if (kind == Kind.STORE) {
            storeSites++;
        } else {
            copySites++;
        }
        pendingSites.add(new PendingSite(site, target));
    }

    /** Registers a site under the objects it may go into, once the stores that tell what a saturated target holds are known. */
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
            System.err.println("THREADESCAPE registered " + site.what.get() + " into " + count + " objects: " + names + " any " + target.any().stream().map(AnalysisType::toJavaName).toList() + " from " + why.summary(rawTarget));
        }
        for (AnalysisObject object : target.objectsIn(bb)) {
            if (site.kind != Kind.CLONE && object.isEmptyObjectArrayConstant(bb)) {
                // Nothing can be stored into an array without elements.
                continue;
            }
            sitesByObject.computeIfAbsent(object, k -> new ArrayList<>(2)).add(site);
        }
        for (AnalysisType type : target.any()) {
            sitesByType.computeIfAbsent(type, k -> new ArrayList<>(2)).add(site);
        }
    }

    /** A store the analysis models by nothing: a site into what it stores into, or a store into who knows what. */
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

    /** What the flows of a method may hold, over every context the method was analysed in. */
    Held heldOf(PointsToAnalysisMethod method, List<TypeFlow<?>> originals) {
        Held held = Held.NOTHING;
        for (TypeFlow<?> original : originals) {
            if (method.getTypeFlow() instanceof com.oracle.graal.pointsto.flow.CallSiteSensitiveMethodTypeFlow sensitive) {
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
     * What a call does with its arguments, by what the facts say of its callees. A method the
     * facts don't have may share them and what it returns; a method with an effect the facts
     * can't name links the objects of different arguments.
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
                // What it does is known: it stores where its arguments say, or nowhere.
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

    /** A call to a method the facts don't have: its arguments and its result are shared. */
    private void shareOpaqueCall(AnalysisMethod caller, InvokeTypeFlow invoke, AnalysisMethod culprit) {
        for (TypeFlow<?> argument : invoke.getActualParameters()) {
            if (argument != null) {
                why.because(() -> "argument of a call in " + caller.format("%H.%n") + " to " + (culprit == null ? "a method without targets" : culprit.format("%H.%n") + ", which the facts don't have") +
                                (argument.isSaturated() ? " (saturated flow)" : ""), null);
                escape.share(reader.held(argument, true));
            }
        }
        if (invoke.getActualReturn() != null) {
            why.because(() -> "result of a call in " + caller.format("%H.%n") + " to " + (culprit == null ? "a method without targets" : culprit.format("%H.%n") + ", which the facts don't have"), null);
            escape.share(reader.held(invoke.getActualReturn(), true));
        }
    }

    /** A call to a method with an effect the facts can't name: the objects of different arguments are linked. */
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
     * Whether a method stores a reference at an offset in the object it is given, as the
     * unsafe and variable handle accessors do. Their bodies are one for every field and every
     * object, so what they say about what is stored where merges every call; the arguments of
     * each call say it exactly.
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
     * Whether a method the facts don't have stores no reference and gives back none it wasn't
     * given: the natives of Object and Class that read an object or its class, and the identity
     * hash code. Their behavior is fixed by the language.
     */
    private static boolean isPure(AnalysisMethod method) {
        String owner = method.getDeclaringClass().toJavaName(true);
        String name = method.getName();
        return owner.equals("java.lang.Object") && PURE_OBJECT.contains(name) || owner.equals("java.lang.Class") && PURE_CLASS.contains(name) ||
                        owner.equals("java.lang.System") && name.equals("identityHashCode");
    }

    /**
     * A call to a store accessor stores its last object argument into its first, after the
     * accessor's own, the handle or the unsafe object; with only one, a static field's, it
     * stores it where every thread reaches.
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

    /** The contents of an object a site may go into are shared: what it stores is shared, what it copies from has its contents shared. */
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
                // A clone has the type of what it clones.
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
