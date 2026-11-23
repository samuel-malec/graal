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

import java.lang.ref.Reference;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.regex.Pattern;

import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.export.FlowReader.Held;
import com.oracle.graal.pointsto.export.FlowReader.Source;
import com.oracle.graal.pointsto.export.PublishingSites.Link;
import com.oracle.graal.pointsto.export.PublishingSites.PendingSite;
import com.oracle.graal.pointsto.export.PublishingSites.Site;
import com.oracle.graal.pointsto.flow.InvokeTypeFlow;
import com.oracle.graal.pointsto.flow.MethodFlowsGraph;
import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.flow.context.object.AnalysisObject;
import com.oracle.graal.pointsto.flow.context.object.ConstantContextSensitiveObject;
import com.oracle.graal.pointsto.heap.ImageHeapConstant;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisField;
import com.oracle.graal.pointsto.meta.PointsToAnalysisMethod;
import com.oracle.graal.pointsto.typestate.TypeState;
import com.oracle.graal.pointsto.typestore.ArrayElementsTypeStore;
import com.oracle.graal.pointsto.typestore.FieldTypeStore;

import jdk.vm.ci.code.BytecodePosition;

/**
 * Thread escape: computes which analysis objects another thread may reach ("shared" objects). A
 * lock or volatile access on an object that is not shared cannot synchronize with another thread.
 * <p>
 * The computation is a mark phase, like a garbage collector's, starting from what every thread
 * can see:
 * <ul>
 * <li><b>Roots.</b> Contents of static fields, the image heap, threads, the references the
 * reference handler thread processes, and anything passed to or returned from a method the
 * analysis has no facts for (such as a native method).</li>
 * <li><b>Propagation.</b> An object stored into a shared object becomes shared. Stores are the
 * analysis' store flows: field stores, array stores and unsafe stores. Array copies and clones
 * share the source's contents once the destination's contents are shared.</li>
 * <li><b>Summaries.</b> The analysis may name an object by its type alone (a summary for "any
 * object of exactly this type") or by its allocation site. A summary is shared when any object it
 * stands for is, and if a summary is shared in its own right, every object of the type is.</li>
 * </ul>
 * <p>
 * <b>Calls with unknown effects.</b> Most unknown effects belong to the VM (class initialization,
 * native transitions, identity hash codes) and store no references. Those that can, such as raw
 * reference writes, are assumed to store only into objects reachable from the call's arguments,
 * so the arguments of one call are linked: once one is shared, all are. Calls into code the
 * analysis can't see at all (function pointers, reflection) share all their arguments.
 * <p>
 * <b>Saturated flows.</b> When a flow holds too many types the analysis stops tracking its
 * contents. What it holds is then rebuilt from the flows that feed it (this needs
 * {@code -H:+TrackInputFlows}): exact inputs as they are, loads by what was stored into the loaded
 * field or array, and anything else as any object of the flow's declared type. All stores are
 * collected before propagation starts, so store targets and call arguments are as precise as the
 * stores allow.
 * <p>
 * <b>Assumptions.</b> Some facts the analysis can't show are assumed, each under a name
 * ({@link PointsToExport#ASSUMPTIONS}); with none, the result follows from the analysis alone:
 * <ul>
 * <li>{@code thread-confined}: a thread's park blocker and thread locals are read only by that
 * thread.</li>
 * <li>{@code vm-fields}: the VM's own classes' static and instance fields are read only by the
 * VM.</li>
 * <li>{@code vm-code}: VM code stores references only where VM code reads them; for example,
 * putting a locked object into the monitor table doesn't share it. This covers the VM's array and
 * unsafe stores and its stores into its own classes' fields, but not into JDK or program classes'
 * fields (a thread's holder is created by the VM and read by the JDK).</li>
 * <li>{@code handler-references}: the reference handler thread never reads a reference's
 * referent, so a reference can be shared without its referent.</li>
 * <li>{@code entry-points}: the VM's calls into the analysis roots (C entry points, JNI, runtime
 * linkage) pass only objects that are already shared, and don't publish what the roots return or
 * throw. The analysis injects every object of a parameter's declared type into a root's
 * parameters; with this assumption, that injection is ignored when a flow is rebuilt.</li>
 * </ul>
 * <p>
 * <b>Classes.</b> {@link FlowReader} says what a flow may hold, also when it saturated.
 * {@link PublishingSites} turns stores, copies, clones and calls into sites that share what they
 * move once their target's contents are shared. {@link StoredPlaces} tracks what was stored into a
 * field or into arrays. {@link SharingExplanation} records why an object is shared, on request.
 * This class holds the shared sets, the roots and the worklist.
 */
final class ThreadEscape {

    /** How completely the facts describe a method. */
    enum Described {
        /** Fully, or only with unknown effects that store no reference. */
        WHOLE,
        /** The method has facts, but an unknown effect or call that may store a reference. */
        UNKNOWN_EFFECT,
        /** No facts at all, e.g. a native method. */
        NOTHING
    }

    /**
     * A reference store that the analysis doesn't model when it is conservative about unsafe accesses:
     * an unsafe put, a CAS, an atomic exchange. Holds the flows of the target object and of the stored
     * value (in the method's first graph), or null where no flow exists.
     */
    record UnsafeStore(PointsToAnalysisMethod method, String where, List<TypeFlow<?>> base, List<TypeFlow<?>> value, AnalysisType valueType) {
    }

    /**
     * A call with no type flow, into code the analysis can't see (a function pointer, a reflective
     * call). Holds the flows of each object argument, in the method's first graph.
     */
    record OpaqueCall(PointsToAnalysisMethod method, String where, List<List<TypeFlow<?>>> arguments) {
    }

    /** The package of the VM's own classes. */
    static final String VM = "com.oracle.svm.";

    /**
     * Parts of the analysis to switch off, for testing: each one must break the publication examples,
     * which shows it matters. Given as
     * {@code -Dsideeffects.controlLeaveOut=static,field,array,copy,handle,opaque,imageheap,summaries}:
     * a kind of site; {@code imageheap} (leave image-heap summaries out of the roots); or
     * {@code summaries} (a shared summary no longer shares every object of its type).
     */
    static final Set<String> LEAVE_OUT = Set.of(System.getProperty("sideeffects.controlLeaveOut", "").split(","));

    /** Thread fields that by design only the thread itself reads, for {@code thread-confined}. */
    private static final Set<String> THREAD_CONFINED = Set.of("parkBlocker", "threadLocals");

    /** Print progress ({@code -Dsideeffects.progress=true}). */
    static final boolean PROGRESS = Boolean.getBoolean("sideeffects.progress");

    final FlowReader reader;
    final StoredPlaces places;
    final PublishingSites sites;
    final SharingExplanation why;
    /** Types whose sharing should be explained (a regular expression), or null. */
    final Pattern explain;

    final PointsToAnalysis bb;
    final AnalysisUniverse universe;

    /** The assumptions in effect, by name. */
    final Set<String> assumptions;

    /** Whether to also read what each field's flow says it may hold, in addition to the stores. */
    final boolean readFlows = System.getProperty("sideeffects.readFlows") != null;

    final AnalysisType objectType;

    /** Every object some flow of a reachable method may hold. */
    final Set<AnalysisObject> known = new LinkedHashSet<>();

    /** Known objects not yet shared, by type. */
    private final Map<AnalysisType, List<AnalysisObject>> unshared = new HashMap<>();

    /** Known objects whose contents are not yet shared, by type. */
    final Map<AnalysisType, List<AnalysisObject>> uncontained = new HashMap<>();

    /** Objects another thread may reach. */
    final Set<AnalysisObject> shared = new HashSet<>();

    /** Objects whose contents another thread may reach (a superset of the shared ones). */
    final Set<AnalysisObject> contents = new HashSet<>();

    /** References shared only with the reference handler thread; their referents are not shared. */
    private final Set<AnalysisObject> handlerOnly = new HashSet<>();

    /** Summaries shared only because an object they stand for is. */
    private final Set<AnalysisObject> derivedShared = new HashSet<>();

    /** Summaries whose contents are shared only because an object they stand for has shared contents. */
    private final Set<AnalysisObject> derivedContents = new HashSet<>();

    /** Worklist: objects newly shared, or with newly shared contents, not processed yet. */
    private final Deque<AnalysisObject> work = new ArrayDeque<>();

    /** Objects whose shared contents have been processed. */
    private final Set<AnalysisObject> contentDone = new HashSet<>();
    /** Shared objects that have been processed. */
    private final Set<AnalysisObject> fullDone = new HashSet<>();
    /** References whose referent has been processed. */
    private final Set<AnalysisObject> referentDone = new HashSet<>();

    /** Declared types of saturated flows whose objects are all shared. */
    private final Set<AnalysisType> anyOf = new HashSet<>();

    /** Declared types of saturated flows whose objects all have shared contents. */
    final Set<AnalysisType> anyContentsOf = new HashSet<>();

    /** Flow states already shared, by identity (the analysis shares one state between many flows). */
    final Set<TypeState> reached = Collections.newSetFromMap(new IdentityHashMap<>());

    /** Exact types of which some object is shared. */
    private final Set<AnalysisType> sharedTypes = new HashSet<>();

    /** Exact types of which some object has shared contents. */
    private final Set<AnalysisType> contentTypes = new HashSet<>();

    /** Deferred until all sites are collected: the calls, static stores and unsafe stores that share directly. */
    final List<Runnable> afterCollection = new ArrayList<>();

    private ThreadEscape(PointsToAnalysis bb, AnalysisUniverse universe, Function<AnalysisMethod, Described> described, boolean compiled, Set<String> assumptions, List<UnsafeStore> unsafeStores,
                    List<OpaqueCall> opaqueCalls) {
        this.bb = bb;
        this.universe = universe;
        this.assumptions = assumptions;
        this.objectType = bb.getMetaAccess().lookupJavaType(Object.class);
        String pattern = System.getProperty("sideeffects.explainSharing");
        this.explain = pattern == null ? null : Pattern.compile(pattern);
        this.reader = new FlowReader(this);
        this.places = new StoredPlaces(this);
        this.sites = new PublishingSites(this, described, compiled, unsafeStores, opaqueCalls);
        this.why = new SharingExplanation(this);
        reader.connect(why);
        places.connect(reader, why);
        sites.connect(reader, places, why);
        why.connect(places);
    }

    /**
     * Returns the names of the shared objects, as {@link GraphExport.PointsTo#objectName} gives them.
     * {@code described} says how completely the facts describe each method, and {@code assumptions}
     * which assumptions to make.
     */
    static TreeSet<String> sharedObjects(PointsToAnalysis bb, AnalysisUniverse universe, Function<AnalysisMethod, Described> described, boolean compiled, Set<String> assumptions,
                    List<UnsafeStore> unsafeStores, List<OpaqueCall> opaqueCalls) {
        ThreadEscape escape = new ThreadEscape(bb, universe, described, compiled, assumptions, unsafeStores, opaqueCalls);
        escape.run();
        if (escape.explain != null) {
            escape.why.explainSharing();
        }
        TreeSet<String> names = new TreeSet<>();
        for (AnalysisObject object : escape.shared) {
            names.add(GraphExport.PointsTo.objectName(object));
        }
        return names;
    }

    private void run() {
        long start = System.nanoTime();
        collectSites();
        start = PointsToExport.step("thread escape: known objects and sites", start);
        // All stores are known now, so sites can resolve their targets and direct sharing can be applied.
        resolveSites(start);
        start = PointsToExport.step("thread escape: sites and calls resolved", start);
        shareRoots();
        start = PointsToExport.step("thread escape: roots", start);
        spread();
        PointsToExport.step("thread escape: reachable objects", start);
        if (PROGRESS) {
            PointsToExport.diagnostics().println("THREADPROGRESS done: places shared " + places.shareVisits + ", closures " + places.closures.size() + ", visits " + places.visits + ", children " +
                            places.childrenSeen + ", shared " + shared.size());
        }
        if (explain != null) {
            PointsToExport.diagnostics().println("THREADESCAPE " + sites.storeSites + " store sites, " + sites.copySites + " copy and clone sites, " + sites.linkedCalls +
                            " calls that link their arguments");
        }
    }

    /** Collects every object some flow holds and creates a site for every store, copy, clone and call. Shares nothing yet. */
    private void collectSites() {
        for (AnalysisMethod method : universe.getMethods()) {
            if (!analysed(method)) {
                continue;
            }
            for (MethodFlowsGraph graph : ((PointsToAnalysisMethod) method).getTypeFlow().getFlows()) {
                for (TypeFlow<?> flow : graph.flows()) {
                    reader.collect(flow, known);
                    if (flow.isFlowEnabled()) {
                        sites.sites(method, flow);
                    }
                }
                for (InvokeTypeFlow invoke : graph.getInvokes()) {
                    sites.call(method, invoke);
                }
            }
        }
        for (UnsafeStore store : sites.unsafeStores) {
            sites.unsafeStore(store);
        }
        for (OpaqueCall call : sites.opaqueCalls) {
            if (!inVirtualMachine(call.method()) && !LEAVE_OUT.contains("opaque")) {
                afterCollection.add(() -> shareArguments(call));
            }
        }
    }

    /** Shares every argument of a call into unseen code; an argument without a flow may be any object. */
    private void shareArguments(OpaqueCall call) {
        for (List<TypeFlow<?>> argument : call.arguments()) {
            why.because(() -> "an argument of a call to code the analysis can't see, in " + call.where(), null);
            if (argument == null) {
                if (explain != null) {
                    PointsToExport.diagnostics().println("THREADESCAPE an argument of a call to code the analysis can't see, in " + call.where() + ", has no flow");
                }
                addAnyOf(objectType);
            } else {
                share(sites.heldOf(call.method(), argument));
            }
        }
    }

    /**
     * Attaches each site to the objects it may store into (now that all stores, and so all saturated
     * targets, are known), and applies what calls, static stores and unsafe stores share directly.
     */
    private void resolveSites(long start) {
        int registered = 0;
        for (PendingSite pending : sites.pendingSites) {
            sites.register(pending.site(), pending.target());
            if (PROGRESS && ++registered % 2000 == 0) {
                PointsToExport.diagnostics().println("THREADPROGRESS registered " + registered + " of " + sites.pendingSites.size() + " sites; closures " + places.closures.size() + ", places " +
                                places.placeTable.size() +
                                ", meets " + reader.meets.size() + ", visits " + places.visits + ", children " + places.childrenSeen + ", " + (System.nanoTime() - start) / 1_000_000 + " ms");
            }
        }
        sites.pendingSites.clear();
        afterCollection.forEach(Runnable::run);
        afterCollection.clear();
    }

    /** Shares the roots (static fields, image heap, threads, references), then groups the remaining objects by type for {@link #shareAll}. */
    private void shareRoots() {
        AnalysisType thread = bb.getMetaAccess().lookupJavaType(Thread.class);
        AnalysisType reference = bb.getMetaAccess().lookupJavaType(Reference.class);
        shareStaticFields();
        shareImageHeap();
        shareThreadsAndReferences(thread, reference);
        for (AnalysisObject object : known) {
            if (!shared.contains(object)) {
                unshared.computeIfAbsent(object.type(), type -> new ArrayList<>()).add(object);
            }
            if (!contents.contains(object)) {
                uncontained.computeIfAbsent(object.type(), type -> new ArrayList<>()).add(object);
            }
        }
    }

    /**
     * What static fields may hold, as their flows say: all static fields when reading field flows,
     * otherwise only those accessed through unsafe (any unsafe store may write them). Other static
     * stores share what they store directly.
     */
    private void shareStaticFields() {
        if (readFlows) {
            for (AnalysisField field : universe.getFields()) {
                if (field.isStatic() && field instanceof PointsToAnalysisField pointsTo && !isPrivate(field)) {
                    why.because(() -> "static field " + field.format("%H.%n"), null);
                    reach(pointsTo.getStaticFieldFlow(), field.getType());
                }
            }
        } else if (!bb.analysisPolicy().useConservativeUnsafeAccess() && !universe.getUnsafeAccessedStaticFields().isEmpty()) {
            // The analysis lets every unsafe store write the static fields accessed through unsafe, whatever its target.
            for (AnalysisField field : universe.getUnsafeAccessedStaticFields()) {
                if (!isPrivate(field) && field instanceof PointsToAnalysisField pointsTo) {
                    why.because(() -> "static field " + field.format("%H.%n") + ", accessed through unsafe", null);
                    reach(pointsTo.getStaticFieldFlow(), field.getType());
                }
            }
        }
    }

    /**
     * Every thread can reach the image heap, whose types the snapshot lists. A summary of such a type
     * stands for the image-heap objects, not for objects the program allocates.
     */
    private void shareImageHeap() {
        if (universe.getHeapScanner() != null && !LEAVE_OUT.contains("imageheap")) {
            for (Map.Entry<AnalysisType, Set<ImageHeapConstant>> entry : universe.getHeapScanner().getImageHeap().getReachableObjects().entrySet()) {
                if (!entry.getValue().isEmpty() && !entry.getKey().isPrimitive()) {
                    AnalysisObject summary = entry.getKey().getContextInsensitiveAnalysisObject();
                    derivedShared.add(summary);
                    derivedContents.add(summary);
                    why.because(() -> "an object of the image heap", null);
                    share(summary);
                }
            }
        }
    }

    /** Shares the image heap's constants, the threads, and the references the reference handler processes. */
    private void shareThreadsAndReferences(AnalysisType thread, AnalysisType reference) {
        for (AnalysisObject object : known) {
            if (object instanceof ConstantContextSensitiveObject || thread.isAssignableFrom(object.type())) {
                why.because(() -> object instanceof ConstantContextSensitiveObject ? "an image heap constant" : "a thread", null);
                share(object);
            } else if (reference.isAssignableFrom(object.type())) {
                why.because(() -> "a reference", null);
                if (assumptions.contains("handler-references")) {
                    shareForHandler(object);
                } else {
                    share(object);
                }
            }
        }
    }

    /** Propagates sharing from the roots until nothing changes: objects, their contents, and all objects of a type once any is. */
    private void spread() {
        Set<AnalysisType> expandedShared = new HashSet<>();
        Set<AnalysisType> expandedContents = new HashSet<>();
        do {
            while (!work.isEmpty()) {
                process(work.poll());
            }
            for (AnalysisType type : new HashSet<>(anyOf)) {
                if (expandedShared.add(type)) {
                    why.because(() -> "any " + type.toJavaName() + " (" + why.anyOfHow.get(type) + ")", why.anyOfFrom.get(type));
                    shareAll(type, unshared, true);
                }
            }
            for (AnalysisType type : new HashSet<>(anyContentsOf)) {
                if (expandedContents.add(type)) {
                    why.because(() -> "the contents of any " + type.toJavaName() + " (" + why.anyOfHow.get(type) + ")", why.anyOfFrom.get(type));
                    shareAll(type, uncontained, false);
                }
            }
        } while (!work.isEmpty());
    }

    /** Processes one object that became shared or got shared contents. */
    private void process(AnalysisObject object) {
        if (contentDone.add(object)) {
            contentsOf(object);
        }
        if (shared.contains(object) && fullDone.add(object)) {
            sharedObject(object);
        }
        if (!handlerOnly.contains(object) && referentDone.add(object)) {
            referentOf(object);
        }
    }

    /** The object's contents became shared: share what was stored into it and what its fields may hold. */
    private void contentsOf(AnalysisObject object) {
        AnalysisType type = object.type();
        // A summary and the objects it stands for have their contents shared together.
        if (object.isContextInsensitiveObject()) {
            if (!derivedContents.contains(object) && !LEAVE_OUT.contains("summaries")) {
                why.because(() -> "the summary of " + type.toJavaName() + ", whose contents are shared", object);
                List<AnalysisObject> same = uncontained.remove(type);
                if (same != null) {
                    same.forEach(this::shareContents);
                }
            }
        } else {
            AnalysisObject summary = type.getContextInsensitiveAnalysisObject();
            if (!contents.contains(summary)) {
                derivedContents.add(summary);
                why.because(() -> "the summary of " + type.toJavaName() + ", which stands for an object with shared contents", object);
                shareContents(summary);
            }
        }
        List<Site> into = sites.sitesByObject.get(object);
        if (into != null) {
            fire(into, object, false);
        }
        if (contentTypes.add(type)) {
            for (Map.Entry<AnalysisType, List<Site>> entry : sites.sitesByType.entrySet()) {
                if (entry.getKey().isAssignableFrom(type)) {
                    fire(entry.getValue(), object, false);
                }
            }
        }
        if (readFlows) {
            for (FieldTypeStore store : object.getExistingInstanceFieldTypeStores()) {
                AnalysisField field = store.field();
                if (!isPrivate(field) && !isReferent(field)) {
                    why.because(() -> "field " + field.format("%H.%n") + (store.writeFlow().isSaturated() ? " (saturated flow)" : ""), object);
                    reach(store.writeFlow(), field.getType());
                }
            }
        }
        if (readFlows || !bb.analysisPolicy().aliasArrayTypeFlows()) {
            // With aliased arrays, all arrays share one element flow holding whatever was stored into any array.
            ArrayElementsTypeStore elements = type.isArray() && !bb.analysisPolicy().aliasArrayTypeFlows() ? object.getArrayElementsTypeStore() : null;
            if (elements != null && elements.writeFlow() != null) {
                why.because(() -> "elements", object);
                reach(elements.writeFlow(), type.getComponentType());
            }
        }
    }

    /** Shares a reference's referent (which the reference handler doesn't read). */
    private void referentOf(AnalysisObject object) {
        List<Site> into = sites.sitesByObject.get(object);
        if (into != null) {
            fire(into, object, true);
        }
        if (readFlows) {
            for (FieldTypeStore store : object.getExistingInstanceFieldTypeStores()) {
                if (isReferent(store.field())) {
                    why.because(() -> "field " + store.field().format("%H.%n"), object);
                    reach(store.writeFlow(), store.field().getType());
                }
            }
        }
    }

    /** Fires the sites that store into the object: stores into a referent, or all other sites. */
    private void fire(List<Site> into, AnalysisObject object, boolean referents) {
        for (Site site : into) {
            boolean intoReferent = site.field != null && isReferent(site.field);
            if (intoReferent == referents) {
                sites.fire(site, object);
            }
        }
    }

    /** The object became shared: calls it is passed to share their other arguments. */
    private void sharedObject(AnalysisObject object) {
        AnalysisType type = object.type();
        // A summary and the objects it stands for are shared together.
        if (object.isContextInsensitiveObject()) {
            if (!derivedShared.contains(object) && !LEAVE_OUT.contains("summaries")) {
                why.because(() -> "the summary of " + type.toJavaName() + ", which is shared", object);
                List<AnalysisObject> same = unshared.remove(type);
                if (same != null) {
                    same.forEach(this::share);
                }
            }
        } else {
            AnalysisObject summary = type.getContextInsensitiveAnalysisObject();
            if (!shared.contains(summary)) {
                derivedShared.add(summary);
                why.because(() -> "the summary of " + type.toJavaName() + ", which stands for a shared object", object);
                share(summary);
            }
        }
        List<Link> passed = sites.links.get(object);
        if (passed != null) {
            passed.forEach(link -> sites.spread(link, object));
        }
        if (sharedTypes.add(type)) {
            for (Map.Entry<AnalysisType, List<Link>> entry : sites.linksByType.entrySet()) {
                if (entry.getKey().isAssignableFrom(type)) {
                    entry.getValue().forEach(link -> sites.spread(link, object));
                }
            }
        }
    }

    /** Whether a flow comes from VM code: what it passes on is not something program code stores. */
    boolean inVirtualMachine(TypeFlow<?> flow) {
        return assumptions.contains("vm-code") && flow.getSource() instanceof BytecodePosition position && position.getMethod() != null &&
                        position.getMethod().getDeclaringClass().toJavaName(true).startsWith(VM);
    }

    /** Whether a method is VM code, for the {@code vm-code} assumption. */
    boolean inVirtualMachine(AnalysisMethod method) {
        return assumptions.contains("vm-code") && method.getDeclaringClass().toJavaName(true).startsWith(VM);
    }

    /** Whether an assumption says no other thread reads this field. */
    boolean isPrivate(AnalysisField field) {
        if (assumptions.isEmpty()) {
            return false;
        }
        String owner = field.getDeclaringClass().toJavaName(true);
        return assumptions.contains("thread-confined") && owner.equals("java.lang.Thread") && THREAD_CONFINED.contains(field.getName()) ||
                        assumptions.contains("vm-fields") && owner.startsWith(VM);
    }

    /** Whether the field is {@code Reference.referent}. */
    private static boolean isReferent(AnalysisField field) {
        return field.getName().equals("referent") && field.getDeclaringClass().toJavaName(true).equals("java.lang.ref.Reference");
    }

    /** Shares everything a value may hold: its objects, any object of its types, and what its places hold. */
    void share(Held held) {
        for (AnalysisObject object : held.objectsIn(bb)) {
            share(object);
        }
        held.any().forEach(this::addAnyOf);
        for (Source stored : held.stored()) {
            if (places.claim(stored, false)) {
                places.shareSource(stored, false);
            }
        }
    }

    /** Shares the contents of everything a value may hold. */
    void shareContents(Held held) {
        for (AnalysisObject object : held.objectsIn(bb)) {
            shareContents(object);
        }
        for (AnalysisType type : held.any()) {
            if (anyContentsOf.add(type) && explain != null) {
                why.recordAnyOf(type);
            }
        }
        for (Source stored : held.stored()) {
            if (places.claim(stored, true)) {
                places.shareSource(stored, true);
            }
        }
    }

    /** Shares the known objects of a type and its subtypes, then drops them from the pending sets, so each type is tested once. */
    private void shareAll(AnalysisType type, Map<AnalysisType, List<AnalysisObject>> buckets, boolean wholly) {
        for (Iterator<Map.Entry<AnalysisType, List<AnalysisObject>>> it = buckets.entrySet().iterator(); it.hasNext();) {
            Map.Entry<AnalysisType, List<AnalysisObject>> objects = it.next();
            if (type.isAssignableFrom(objects.getKey())) {
                objects.getValue().forEach(wholly ? this::share : this::shareContents);
                it.remove();
            }
        }
    }

    /** Whether the analysis reached the method and created its flows. */
    static boolean analysed(AnalysisMethod method) {
        return method.isReachable() && method instanceof PointsToAnalysisMethod ptm && ptm.getTypeFlow().flowsGraphCreated();
    }

    /**
     * Shares what a flow may hold; for a saturated flow, any object of its declared type. The analysis
     * shares one state between many flows, so each state is processed once.
     */
    private void reach(TypeFlow<?> flow, AnalysisType declared) {
        if (flow.isSaturated()) {
            if (declared != null && !declared.isPrimitive()) {
                addAnyOf(declared);
            }
            return;
        }
        TypeState state = flow.getOutputState(bb);
        if (state == null || state.isPrimitive()) {
            return;
        }
        if (reached.add(state)) {
            for (AnalysisObject object : state.objects(bb)) {
                share(object);
            }
        }
    }

    /** Marks every object of the type as shared; {@link #spread} processes it. */
    void addAnyOf(AnalysisType type) {
        if (anyOf.add(type) && explain != null) {
            why.recordAnyOf(type);
        }
    }

    /** Shares an object and its contents. A reference previously shared only with the handler now has its referent shared too. */
    void share(AnalysisObject object) {
        if (shared.add(object)) {
            contents.add(object);
            if (explain != null) {
                why.recordShared(object);
            }
            work.add(object);
        } else if (handlerOnly.remove(object)) {
            // Now shared for another reason too, so its referent is reachable.
            if (explain != null) {
                why.recordCause(object);
            }
            work.add(object);
        }
    }

    /** Shares a reference with the reference handler thread only, without its referent. */
    private void shareForHandler(AnalysisObject object) {
        if (shared.add(object)) {
            contents.add(object);
            handlerOnly.add(object);
            if (explain != null) {
                why.recordCause(object);
            }
            work.add(object);
        }
    }

    /** Shares an object's contents, but not the object. */
    void shareContents(AnalysisObject object) {
        if (contents.add(object)) {
            if (explain != null) {
                why.recordCause(object);
            }
            work.add(object);
        }
    }
}
