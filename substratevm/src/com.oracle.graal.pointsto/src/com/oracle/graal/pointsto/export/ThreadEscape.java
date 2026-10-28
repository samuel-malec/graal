package com.oracle.graal.pointsto.export;

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

/**
 * Which objects of the points-to analysis another thread may reach. An object is shared when
 * something every thread reaches holds it, or when it is held by a shared object, or put into one.
 *
 * <p>
 * What every thread reaches: the contents of static fields; the image heap, whose objects are of
 * the types the snapshot lists; threads and the references the reference handler thread
 * processes; and what a call to a method the facts don't have at all, such as a native, may be
 * given or give back.
 *
 * <p>
 * What goes into an object is what the stores into it say. A store into a field, into an array,
 * or an unsafe store, shares what it stores once an object it may store into is shared, or has
 * its contents shared. A copy between arrays, and a clone, shares the contents of what it copies
 * from once the object it copies into has them. The sites are the flows the analysis made for
 * them. The analysis's own answer, what each field's flow says it may hold, merges the stores
 * of every call to a method into one, and is only read when asked to, or where it is the only
 * answer there is: a field accessed through unsafe, and an array when arrays have a flow of
 * their own.
 *
 * <p>
 * The analysis may name an object by its type alone, a summary that stands for any object of
 * exactly that type, or by where it was allocated. The summary is shared when an object it may
 * stand for is; and when the summary is shared on its own account, any object of the type is,
 * for it may be the one that was. The same goes for having contents shared.
 *
 * <p>
 * A call is described by what the facts say of its callees. A method the facts have, but with an
 * effect or a call they can't name, is an analysed method like any other except for that effect.
 * Most of those effects are the virtual machine's own: a class's initialization, a transition to
 * native code, an identity hash code. None of them stores a reference an object was given. The
 * ones that can, such as a raw write of a reference, we assume store references only into objects
 * reachable from the call's arguments: they may copy a reference from one object passed to the
 * call into another, but publish nothing else. In one call they can only meet the objects passed
 * in that call, one per argument, so the objects of different arguments are linked: once one of
 * them is shared, all the objects the other arguments may be are. A call with one argument that
 * is an object links nothing. Without facts for {@code Thread.currentThread}, the standalone
 * analysis never sees {@code new Thread(task)} store the task, for instance, which links the
 * thread, shared as every thread is, with the task.
 *
 * <p>
 * The analysis gives up on a flow that holds many types: it is saturated, and stops saying what
 * it holds. What it held is rebuilt from the flows that feed it (the analysis must have recorded
 * them, {@code -H:+TrackInputFlows}): where they are exact, what they hold; where one loads from
 * a field or from an array, what the stores into it say, restricted to the types the load gives;
 * where nothing is known, any object of the flow's type. Every store is collected before any of
 * this is used, so that the base of a store and the arguments of a call are what the stores say
 * they are, not any object of their declared type.
 *
 * <p>
 * A call through a function pointer, to code the analysis can't see, may keep every object it is
 * given: its arguments are shared. A reflective call is one.
 *
 * <p>
 * What the analysis can't show, we can assume, one named assumption at a time
 * ({@link PointsToExport#ASSUMPTIONS}); with none, the answer follows from the analysis alone:
 * <ul>
 * <li>{@code thread-confined}: the fields a thread keeps to itself by design, the object it
 * parks on and its thread locals, are never read by another thread.
 * <li>{@code vm-fields}: the state of the virtual machine's own classes, their static fields
 * and the fields of their objects, is read only by the virtual machine.
 * <li>{@code vm-code}: the virtual machine's own code stores references only where the virtual
 * machine reads them. Where a program's object goes through the virtual machine, as a locked
 * object goes into the monitor table, the code that puts it there does not share it. This is
 * taken for the virtual machine's stores into arrays and by unsafe access, and into the fields of its
 * own classes; its stores into fields of the JDK's and the program's classes count, as they are
 * read by the code of those (a thread's holder is made by the virtual machine, and read by the JDK).
 * <li>{@code handler-references}: the reference handler thread processes the references the
 * collector found, and never reads their referents: a reference is shared for it without its
 * referent.
 * <li>{@code entry-points}: the callers of the analysis' roots, which are the virtual machine's
 * (C entry points, JNI, runtime linkage), pass only objects that are shared already, and keep
 * nothing a root returns or throws where another thread reaches it. The analysis does not know
 * the callers and injects every object of the declared type into a root's parameters; with this
 * assumption that injection does not count when a flow is rebuilt.
 * </ul>
 *
 * <p>
 * The work is divided among classes of this package. {@link FlowReader} says what a flow may hold, also
 * when it saturated. {@link PublishingSites} turns the program's stores, copies, clones and calls into sites that
 * share what they move once the objects they move it into have shared contents. {@link StoredPlaces} says what was
 * stored into a field or into the arrays, and shares it. {@link SharingExplanation} keeps the reasons, when asked
 * to. This class holds what is shared, the roots, and the worklist that spreads sharing.
 */
final class ThreadEscape {

    /** How well the facts describe a method. */
    enum Described {
        /** The facts describe it, or what they can't name stores no reference. */
        WHOLE,
        /** The facts have the method, but it has an effect or a call they can't name that may store a reference. */
        UNKNOWN_EFFECT,
        /** The facts don't have the method at all, such as a native. */
        NOTHING
    }

    /**
     * A store of a reference by a node the analysis, when it is conservative about unsafe access,
     * models by nothing: an unsafe put, a compare-and-swap, an atomic exchange. The flows say what
     * the object stored into, and the value stored, may be, in the graph of the method as it was
     * made first; null when the node's input is something no flow was made for.
     */
    record UnsafeStore(PointsToAnalysisMethod method, String where, List<TypeFlow<?>> base, List<TypeFlow<?>> value, AnalysisType valueType) {
    }

    /**
     * A call the analysis made no flow for, to code it can't see: a call through a function
     * pointer, such as the reflective call of a method. The flows say what each argument that is an
     * object may be, in the graph of the method as it was made first.
     */
    record OpaqueCall(PointsToAnalysisMethod method, String where, List<List<TypeFlow<?>>> arguments) {
    }

    final FlowReader reader;
    final StoredPlaces places;
    final PublishingSites sites;
    final SharingExplanation why;
    /** The types the regular expression names, when asked to explain; otherwise null. */
    final Pattern explain;

    static final String VM = "com.oracle.svm.";

    /**
     * Controls, which must break the publication examples: the kinds of site to leave out
     * ({@code -Dsideeffects.controlLeaveOut=static,field,array,copy,handle,opaque}), {@code imageheap}, which leaves the summaries of the types the image heap
     * holds out of the roots, and {@code summaries}, which stops a shared summary from sharing every object of its type: to see how much of the answer each decides.
     */
    static final Set<String> LEAVE_OUT = Set.of(System.getProperty("sideeffects.controlLeaveOut", "").split(","));

    final PointsToAnalysis bb;
    final AnalysisUniverse universe;

    /** The assumptions made on top of what the analysis shows, by name. */
    final Set<String> assumptions;

    /** Whether to read what each field's flow says it may hold, beside the stores. */
    final boolean readFlows = System.getProperty("sideeffects.readFlows") != null;

    final AnalysisType objectType;

    /** Every object some flow of a reachable method may hold. */
    final Set<AnalysisObject> known = new LinkedHashSet<>();

    /** The known objects not shared yet, and those whose contents are not shared yet, by their type. */
    private final Map<AnalysisType, List<AnalysisObject>> unshared = new HashMap<>();

    final Map<AnalysisType, List<AnalysisObject>> uncontained = new HashMap<>();

    /** The objects another thread may reach; those whose contents it may reach, which these are among. */
    final Set<AnalysisObject> shared = new HashSet<>();

    final Set<AnalysisObject> contents = new HashSet<>();

    /** The shared objects that are shared only for the reference handler thread: their referents are not. */
    private final Set<AnalysisObject> handlerOnly = new HashSet<>();

    /** The summaries shared, or with shared contents, only because an object they stand for is. */
    private final Set<AnalysisObject> derivedShared = new HashSet<>();

    private final Set<AnalysisObject> derivedContents = new HashSet<>();
    private final Deque<AnalysisObject> work = new ArrayDeque<>();
    private final Set<AnalysisObject> contentDone = new HashSet<>();
    private final Set<AnalysisObject> fullDone = new HashSet<>();
    private final Set<AnalysisObject> referentDone = new HashSet<>();

    /** The declared types of the saturated flows that share, or share the contents of, all their objects. */
    private final Set<AnalysisType> anyOf = new HashSet<>();

    final Set<AnalysisType> anyContentsOf = new HashSet<>();

    /** The states of the flows reached, by identity: all their objects are shared. */
    final Set<TypeState> reached = Collections.newSetFromMap(new IdentityHashMap<>());

    /** The exact types some shared object, or an object with shared contents, has. */
    private final Set<AnalysisType> sharedTypes = new HashSet<>();

    private final Set<AnalysisType> contentTypes = new HashSet<>();
    final List<Runnable> afterCollection = new ArrayList<>();
    private static final Set<String> THREAD_CONFINED = Set.of("parkBlocker", "threadLocals");
    static final boolean PROGRESS = Boolean.getBoolean("sideeffects.progress");

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
     * The names of the shared objects, as {@link GraphExport.PointsTo#objectName} gives them.
     * {@code described} says how well the facts describe a method, and {@code assumptions}
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
        // Every store is known: the sites can say which objects they go into, and what is shared outright can be read.
        resolveSites(start);
        start = PointsToExport.step("thread escape: sites and calls resolved", start);
        shareRoots();
        start = PointsToExport.step("thread escape: roots", start);
        spread();
        PointsToExport.step("thread escape: reachable objects", start);
        if (PROGRESS) {
            System.err.println("THREADPROGRESS done: places shared " + places.shareVisits + ", closures " + places.closures.size() + ", visits " + places.visits + ", children " + places.childrenSeen + ", shared " + shared.size());
        }
        if (explain != null) {
            System.err.println("THREADESCAPE " + sites.storeSites + " store sites, " + sites.copySites + " copy and clone sites, " + sites.linkedCalls + " calls that link their arguments");
        }
    }

    /** Collects every object some flow holds, and makes a site of every store, copy, clone and call of the reachable methods. Nothing is shared yet. */
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
                afterCollection.add(() -> {
                    for (List<TypeFlow<?>> argument : call.arguments()) {
                        why.because(() -> "an argument of a call to code the analysis can't see, in " + call.where(), null);
                        if (argument == null) {
                            if (explain != null) {
                                System.err.println("THREADESCAPE an argument of a call to code the analysis can't see, in " + call.where() + ", has no flow");
                            }
                            addAnyOf(objectType);
                        } else {
                            share(sites.heldOf(call.method(), argument));
                        }
                    }
                });
            }
        }
    }

    /**
     * Puts each site under the objects it may go into, now that the stores that tell what a saturated target
     * holds are all known, and shares what the calls, the static stores and the unsafe stores share outright.
     */
    private void resolveSites(long start) {
        int registered = 0;
        for (PendingSite pending : sites.pendingSites) {
            sites.register(pending.site(), pending.target());
            if (PROGRESS && ++registered % 2000 == 0) {
                System.err.println("THREADPROGRESS registered " + registered + " of " + sites.pendingSites.size() + " sites; closures " + places.closures.size() + ", places " + places.placeTable.size() +
                                ", meets " + reader.meets.size() + ", visits " + places.visits + ", children " + places.childrenSeen + ", " + (System.nanoTime() - start) / 1_000_000 + " ms");
            }
        }
        sites.pendingSites.clear();
        afterCollection.forEach(Runnable::run);
        afterCollection.clear();
    }

    /** Shares what every thread reaches: static fields, the image heap, threads and references. */
    private void shareRoots() {
        AnalysisType thread = bb.getMetaAccess().lookupJavaType(Thread.class);
        AnalysisType reference = bb.getMetaAccess().lookupJavaType(java.lang.ref.Reference.class);
        if (readFlows) {
            for (AnalysisField field : universe.getFields()) {
                if (field.isStatic() && field instanceof PointsToAnalysisField pointsTo && !isPrivate(field)) {
                    why.because(() -> "static field " + field.format("%H.%n"), null);
                    reach(pointsTo.getStaticFieldFlow(), field.getType());
                }
            }
        } else if (!bb.analysisPolicy().useConservativeUnsafeAccess() && !universe.getUnsafeAccessedStaticFields().isEmpty()) {
            // The analysis lets every unsafe store write to the static fields accessed through unsafe, whatever it stores into.
            for (AnalysisField field : universe.getUnsafeAccessedStaticFields()) {
                if (!isPrivate(field) && field instanceof PointsToAnalysisField pointsTo) {
                    why.because(() -> "static field " + field.format("%H.%n") + ", accessed through unsafe", null);
                    reach(pointsTo.getStaticFieldFlow(), field.getType());
                }
            }
        }
        // The image heap is what every thread reaches, and the snapshot lists its types. The summary of
        // such a type stands for those objects, not for what the program allocates of the type.
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
        for (AnalysisObject object : known) {
            if (!shared.contains(object)) {
                unshared.computeIfAbsent(object.type(), type -> new ArrayList<>()).add(object);
            }
            if (!contents.contains(object)) {
                uncontained.computeIfAbsent(object.type(), type -> new ArrayList<>()).add(object);
            }
        }
    }

    /** Spreads sharing from the roots until nothing new is shared: objects, their contents, and the objects of a type once any of them is. */
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

    /** What is done for an object that is shared, or whose contents are. */
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

    /** The contents of an object are shared: what is stored into it, and what its fields may hold. */
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
            for (Site site : into) {
                if (site.field == null || !isReferent(site.field)) {
                    sites.fire(site, object);
                }
            }
        }
        if (contentTypes.add(type)) {
            for (Map.Entry<AnalysisType, List<Site>> entry : sites.sitesByType.entrySet()) {
                if (entry.getKey().isAssignableFrom(type)) {
                    for (Site site : entry.getValue()) {
                        if (site.field == null || !isReferent(site.field)) {
                            sites.fire(site, object);
                        }
                    }
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
            // With aliased arrays, all arrays have one elements flow, which holds what was stored into any array.
            ArrayElementsTypeStore elements = type.isArray() && !bb.analysisPolicy().aliasArrayTypeFlows() ? object.getArrayElementsTypeStore() : null;
            if (elements != null && elements.writeFlow() != null) {
                why.because(() -> "elements", object);
                reach(elements.writeFlow(), type.getComponentType());
            }
        }
    }

    /** The referent of a reference, which the reference handler thread doesn't read. */
    private void referentOf(AnalysisObject object) {
        List<Site> into = sites.sitesByObject.get(object);
        if (into != null) {
            for (Site site : into) {
                if (site.field != null && isReferent(site.field)) {
                    sites.fire(site, object);
                }
            }
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

    /** An object is shared: the calls it is passed to share their other arguments. */
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

    /** Whether a flow is the virtual machine's, by its source: what it passes on is not what its code stores. */
    boolean inVirtualMachine(TypeFlow<?> flow) {
        return assumptions.contains("vm-code") && flow.getSource() instanceof jdk.vm.ci.code.BytecodePosition position && position.getMethod() != null &&
                        position.getMethod().getDeclaringClass().toJavaName(true).startsWith(VM);
    }

    boolean inVirtualMachine(AnalysisMethod method) {
        return assumptions.contains("vm-code") && method.getDeclaringClass().toJavaName(true).startsWith(VM);
    }

    /** Whether the field is one that no other thread reads, by an assumption. */
    boolean isPrivate(AnalysisField field) {
        if (assumptions.isEmpty()) {
            return false;
        }
        String owner = field.getDeclaringClass().toJavaName(true);
        return assumptions.contains("thread-confined") && owner.equals("java.lang.Thread") && THREAD_CONFINED.contains(field.getName()) ||
                        assumptions.contains("vm-fields") && owner.startsWith(VM);
    }

    private static boolean isReferent(AnalysisField field) {
        return field.getName().equals("referent") && field.getDeclaringClass().toJavaName(true).equals("java.lang.ref.Reference");
    }

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

    /** Shares the known objects of a type and its subtypes, and forgets them: a type is tested once per type of objects, not once per object. */
    private void shareAll(AnalysisType type, Map<AnalysisType, List<AnalysisObject>> buckets, boolean wholly) {
        for (Iterator<Map.Entry<AnalysisType, List<AnalysisObject>>> it = buckets.entrySet().iterator(); it.hasNext();) {
            Map.Entry<AnalysisType, List<AnalysisObject>> objects = it.next();
            if (type.isAssignableFrom(objects.getKey())) {
                objects.getValue().forEach(wholly ? this::share : this::shareContents);
                it.remove();
            }
        }
    }

    static boolean analysed(AnalysisMethod method) {
        return method.isReachable() && method instanceof PointsToAnalysisMethod ptm && ptm.getTypeFlow().flowsGraphCreated();
    }

    /**
     * What a flow may hold is shared; for a saturated flow, any object of its declared type. A
     * state many flows hold, the analysis keeps once, so it is shared once.
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

    private void reach(TypeFlow<?> flow) {
        reach(flow, flow.getDeclaredType());
    }

    void addAnyOf(AnalysisType type) {
        if (anyOf.add(type) && explain != null) {
            why.recordAnyOf(type);
        }
    }

    void share(AnalysisObject object) {
        if (shared.add(object)) {
            contents.add(object);
            if (explain != null) {
                why.recordShared(object);
            }
            work.add(object);
        } else if (handlerOnly.remove(object)) {
            // Shared for another reason too: its referent is now reachable.
            if (explain != null) {
                why.recordCause(object);
            }
            work.add(object);
        }
    }

    /** Shares a reference for the reference handler thread, which doesn't read its referent. */
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

    void shareContents(AnalysisObject object) {
        if (contents.add(object)) {
            if (explain != null) {
                why.recordCause(object);
            }
            work.add(object);
        }
    }
}
