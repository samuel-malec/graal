package com.oracle.graal.pointsto.export;

import java.io.OutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;

import com.oracle.graal.pointsto.AbstractAnalysisEngine;
import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.flow.AccessFieldTypeFlow;
import com.oracle.graal.pointsto.flow.InvokeTypeFlow;
import com.oracle.graal.pointsto.flow.LoadFieldTypeFlow;
import com.oracle.graal.pointsto.flow.MethodFlowsGraph;
import com.oracle.graal.pointsto.flow.StoreFieldTypeFlow;
import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisMethod;

import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.FieldLocationIdentity;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.NamedLocationIdentity;
import jdk.graal.compiler.nodes.StartNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.java.AbstractNewObjectNode;
import jdk.graal.compiler.nodes.java.AccessFieldNode;
import jdk.graal.compiler.nodes.java.AccessMonitorNode;
import jdk.graal.compiler.nodes.extended.BytecodeExceptionNode;
import jdk.graal.compiler.nodes.extended.MonitorEnter;
import jdk.graal.compiler.nodes.extended.MonitorExit;
import jdk.graal.compiler.nodes.extended.RawLoadNode;
import jdk.graal.compiler.nodes.extended.RawStoreNode;
import jdk.graal.compiler.nodes.java.AbstractUnsafeCompareAndSwapNode;
import jdk.graal.compiler.nodes.java.AtomicReadAndWriteNode;
import jdk.graal.compiler.nodes.type.StampTool;
import jdk.graal.compiler.nodes.java.AccessIndexedNode;
import jdk.graal.compiler.nodes.java.ArrayLengthNode;
import jdk.graal.compiler.nodes.java.ExceptionObjectNode;
import jdk.graal.compiler.nodes.java.FinalFieldBarrierNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.LoadIndexedNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.memory.AbstractWriteNode;
import jdk.graal.compiler.nodes.memory.MemoryAccess;
import jdk.graal.compiler.nodes.memory.MemoryKill;
import jdk.graal.compiler.nodes.memory.OrderedMemoryAccess;
import jdk.graal.compiler.nodes.memory.ReadNode;
import jdk.graal.compiler.nodes.virtual.CommitAllocationNode;
import jdk.graal.compiler.replacements.nodes.BasicArrayCopyNode;
import jdk.graal.compiler.replacements.nodes.ObjectClone;
import jdk.vm.ci.code.BytecodePosition;
import jdk.vm.ci.meta.JavaKind;
import org.graalvm.word.LocationIdentity;

/**
 * Exports what a points-to analysis that has run knows: the facts of every reachable method (the
 * fields it reads and writes, what it allocates, the calls it makes and their targets, the objects
 * each access may touch), and the Graal IR of the program's methods, scheduled, as JSON.
 */
public final class PointsToExport {

    private PointsToExport() {
    }

    /** The VM's own locations the facts name, vm:TLAB.top, by name: a feature in the same build gives them back to Graal. */
    public static final Map<String, LocationIdentity> VM_LOCATIONS = new ConcurrentHashMap<>();

    /**
     * How long each step of the last export took, in nanoseconds: the facts of every reachable method,
     * the report, thread escape, the program's graphs, and writing the JSON.
     */
    public static final Map<String, Long> STEP_NANOS = new ConcurrentHashMap<>();

    /**
     * The nodes that kill any location, and so are effects the facts can't name, but store no
     * reference an object was given: a class's initialization, a transition between Java and
     * native code, a change of the register that holds the current thread, an identity hash code
     * written to an object's header, a barrier, a string search. Raw and unsafe stores of
     * references, atomic updates included, are flows of the analysis, which thread escape
     * reads as stores; a raw write at an address is not, and links the objects of a call.
     */
    private static final Set<String> STORES_NO_REFERENCE = Set.of("EnsureClassInitializedNode", "CEntryPointEnterNode", "CEntryPointLeaveNode", "CEntryPointUtilityNode",
                    "CFunctionPrologueNode", "CFunctionEpilogueNode", "SubstrateIdentityHashCodeNode", "WriteCurrentVMThreadNode", "WriteHeapBaseNode", "WriteCodeBaseNode",
                    "CompareAndSetVMThreadLocalNode", "VaListInitializationNode", "VaListNextArgNode", "ExceptionPathNode", "ValidateNewInstanceClassNode",
                    "SubstrateReflectionGetCallerClassNode", "FinalFieldBarrierNode", "SnippetSubstitutionNode", "ForeignCallNode", "RawStoreNode");

    private interface DescribedAs {
        java.util.function.Function<AnalysisMethod, ThreadEscape.Described> apply(Set<String> analysed, TreeMap<String, TreeSet<String>> unknown, TreeMap<String, TreeSet<String>> unresolved);
    }

    /** How well the facts describe a method: not at all, with an effect or a call they can't name that may store a reference, or whole. */
    private static final DescribedAs describedAs = (analysed, unknown, unresolved) -> method -> {
        String key = GraphExport.methodKey(method);
        if (!analysed.contains(key)) {
            return ThreadEscape.Described.NOTHING;
        }
        TreeSet<String> effects = unknown.get(key);
        return (effects != null && effects.stream().anyMatch(effect -> !STORES_NO_REFERENCE.contains(effect.replaceFirst(" at bci.*", ""))))
                        ? ThreadEscape.Described.UNKNOWN_EFFECT : ThreadEscape.Described.WHOLE;
    };

    /**
     * The assumptions thread escape makes on top of what the analysis shows, by name:
     * {@code thread-confined}, {@code vm-fields}, {@code vm-code}, {@code handler-references} and
     * {@code entry-points}, which {@link ThreadEscape} describes. Set by the feature; none makes the answer follow from the
     * analysis alone.
     */
    public static volatile Set<String> ASSUMPTIONS = System.getProperty("sideeffects.assumptions", "").isEmpty() ? Set.of() : Set.of(System.getProperty("sideeffects.assumptions").split(","));

    /** Packages treated as "not the program under analysis" by default. */
    private static final String[] PLATFORM = {
                    "java.", "javax.", "jdk.", "sun.", "com.sun.",
                    "com.oracle.", "org.graalvm.",
                    "org.ietf.", "org.jcp.", "org.w3c.", "org.xml.",
    };

    /** The program's class-name prefixes, as {@link #isProgramClass(String, String)} takes them. */
    private static volatile String programPrefix = "";

    /** Whether a class belongs to the program under analysis, as the last export was told. */
    public static boolean isProgramClass(String className) {
        return isProgramClass(className, programPrefix);
    }

    /**
     * Whether a class belongs to the program that {@code prefixes} names: comma-separated
     * class-name prefixes, none for every class outside the platform's packages, * for all.
     */
    public static boolean isProgramClass(String className, String prefixes) {
        if (prefixes.equals("*")) {
            return true;
        }
        boolean named = false;
        for (String prefix : prefixes.split(",")) {
            if (!prefix.isEmpty()) {
                named = true;
                if (className.startsWith(prefix)) {
                    return true;
                }
            }
        }
        if (named) {
            return false;
        }
        for (String prefix : PLATFORM) {
            if (className.startsWith(prefix)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Exports the facts of every reachable method, and the graphs of the program's, from an
     * analysis that has run: the standalone analyzer's, or Native Image's own, from a feature.
     * An empty path skips that file; the reports go to {@code report}, null for none.
     * {@code compiled} says the graphs are about to be compiled into an image, so calls the
     * analysis found no target for never happen; {@code programPrefix} names the program, as
     * {@link #isProgramClass(String, String)} takes it.
     */
    public static void export(PointsToAnalysis bb, AnalysisUniverse universe, String jsonPath, String irPath, PrintStream report, boolean compiled, String programPrefix) {
        PointsToExport.programPrefix = programPrefix;
        STEP_NANOS.clear();
        SITE_LABEL_COLLISIONS.set(0);
        long start = System.nanoTime();
        PrintStream out = report != null ? report : new PrintStream(OutputStream.nullOutputStream());
        // Before any name is made: names are keys, and the keys decide the order things are written in.
        GraphExport.nameHiddenClasses(universe.getTypes(), out);
        // Each method's facts are its own: they are collected in parallel, and merged into sorted
        // maps, so the export is the same as one made method by method.
        Facts found = new Facts();
        universe.getMethods().parallelStream()
                        .filter(method -> method.isReachable() && method instanceof PointsToAnalysisMethod ptm && ptm.getTypeFlow().flowsGraphCreated())
                        .map(method -> collect(bb, (PointsToAnalysisMethod) method, compiled))
                        .toList()
                        .forEach(found::merge);
        if (SITE_LABEL_COLLISIONS.get() > 0) {
            System.err.println("SIDEEFFECT " + SITE_LABEL_COLLISIONS.get() + " locks, volatile accesses or waits had the label of another site in their method; their objects were merged");
        }
        TreeMap<String, TreeSet<String>> reads = found.reads;
        TreeMap<String, TreeSet<String>> writes = found.writes;
        TreeMap<String, TreeSet<String>> callees = found.callees;
        TreeSet<String> analysed = found.analysed;
        TreeSet<String> program = found.program;
        TreeSet<String> allocates = found.allocates;
        TreeMap<String, TreeSet<String>> unknown = found.unknown;
        TreeMap<String, TreeSet<String>> acquires = found.acquires;
        TreeMap<String, TreeSet<String>> releases = found.releases;
        TreeMap<String, TreeMap<String, Object>> locks = found.locks;
        TreeMap<String, TreeMap<String, Object>> waits = found.waits;
        TreeMap<String, TreeSet<String>> unresolved = found.unresolved;
        TreeMap<String, TreeSet<String>> accesses = found.accesses;
        TreeMap<String, TreeSet<String>> vmWrites = found.vmWrites;
        TreeMap<String, TreeSet<String>> unknownReads = found.unknownReads;
        TreeMap<String, TreeSet<String>> dead = found.dead;

        start = step("facts", start);
        Set<String> all = new TreeSet<>();
        all.addAll(reads.keySet());
        all.addAll(writes.keySet());
        all.retainAll(program);

        out.println();
        out.println("=== local per-method field effects ===");
        if (all.isEmpty()) {
            out.println("  (nothing reported -- wrong -Ddump.filter, or no reachable");
            out.println("   field accesses in the analysed program?)");
        }
        for (String m : all) {
            out.printf("  %-34s reads=%-28s writes=%s%n",
                            m,
                            reads.getOrDefault(m, new TreeSet<>()),
                            writes.getOrDefault(m, new TreeSet<>()));
        }

        out.println();
        out.println("=== call graph with points-to resolved callees ===");
        for (String m : new TreeSet<>(callees.keySet())) {
            if (!program.contains(m)) {
                continue;
            }
            TreeSet<String> targets = new TreeSet<>();
            for (String t : callees.get(m)) {
                targets.add(isProgramClass(t.substring(0, t.lastIndexOf('.', t.indexOf('(')))) ? t : "<platform>");
            }
            targets.remove("<platform>");
            if (!targets.isEmpty()) {
                out.printf("  %-34s -> %s%n", m, targets);
            }
        }

        out.println();
        out.println("=== reachable fields ===");
        TreeMap<String, boolean[]> fields = new TreeMap<>();
        for (AnalysisField f : universe.getFields()) {
            if (!isProgramClass(f.getDeclaringClass().toJavaName(true))) {
                continue;
            }
            fields.put(GraphExport.fieldName(f), new boolean[]{f.isRead(), f.isWritten()});
        }
        for (var e : fields.entrySet()) {
            out.printf("  %-30s read=%-6s written=%s%n",
                            e.getKey(), e.getValue()[0], e.getValue()[1]);
        }

        out.println();
        out.println("=== synchronization, memory effects the facts can't name, and calls without a target ===");
        for (String m : program) {
            for (String what : acquires.getOrDefault(m, new TreeSet<>())) {
                out.printf("  %-34s acquire: %s%n", m, what);
            }
            for (String what : releases.getOrDefault(m, new TreeSet<>())) {
                out.printf("  %-34s release: %s%n", m, what);
            }
            for (String what : unknown.getOrDefault(m, new TreeSet<>())) {
                out.printf("  %-34s %s%n", m, what);
            }
            for (String what : unresolved.getOrDefault(m, new TreeSet<>())) {
                out.printf("  %-34s unresolved call to %s%n", m, what);
            }
        }

        start = step("report", start);
        TreeSet<String> shared = ThreadEscape.sharedObjects(bb, universe, describedAs.apply(analysed, unknown, unresolved), compiled, ASSUMPTIONS, found.unsafeStores, found.opaqueCalls);
        start = step("thread escape", start);
        // For evaluation: what each assumption adds, from one analysis.
        Map<String, TreeSet<String>> byAssumptions = new TreeMap<>();
        if (System.getProperty("sideeffects.assumptionLayers") != null) {
            for (String assumptions : List.of("", "thread-confined", "thread-confined,vm-fields", "thread-confined,vm-fields,vm-code", "thread-confined,vm-fields,vm-code,handler-references",
                            "thread-confined,vm-fields,vm-code,handler-references,entry-points", "vm-code,entry-points")) {
                byAssumptions.put(assumptions.isEmpty() ? "none" : assumptions, ThreadEscape.sharedObjects(bb, universe, describedAs.apply(analysed, unknown, unresolved), compiled,
                                assumptions.isEmpty() ? Set.of() : Set.of(assumptions.split(",")), found.unsafeStores, found.opaqueCalls));
            }
        }
        // Written method by method, and the shared objects one by one: with allocation sites the facts and the shared objects are each longer than
        // a String can be (2^31 characters).
        Content facts = w -> {
            factsJson(w, analysed, reads, writes, callees, allocates, unknown, acquires, releases, locks, waits, unresolved, accesses, fields, vmWrites, unknownReads, dead);
            w.write(",\n  \"sharedObjects\": ");
            GraphExport.writeJson(w, shared);
            if (!byAssumptions.isEmpty()) {
                w.write(",\n  \"sharedObjectsByAssumptions\": ");
                GraphExport.writeJson(w, byAssumptions);
            }
        };
        if (!jsonPath.isEmpty()) {
            write(jsonPath, w -> {
                w.write("{\n");
                facts.writeTo(w);
                w.write("\n}\n");
            });
            out.println();
            out.println("wrote " + jsonPath);
        }

        if (!irPath.isEmpty()) {
            List<PointsToAnalysisMethod> methods = new ArrayList<>();
            for (AnalysisMethod method : universe.getMethods()) {
                if (method.isReachable() && method instanceof PointsToAnalysisMethod ptm && ptm.getTypeFlow().flowsGraphCreated() &&
                                isProgramClass(method.getDeclaringClass().toJavaName(true))) {
                    methods.add(ptm);
                }
            }
            methods.sort(Comparator.comparing(method -> GraphExport.methodName(method) + " " + GraphExport.stable(method.getSignature().toMethodDescriptor())));
            GraphExport.ObjectNames objectNames = new GraphExport.ObjectNames(bb);
            List<Map<String, Object>> graphs = new ArrayList<>();
            start = step("write", start);
            for (PointsToAnalysisMethod method : methods) {
                graphs.add(GraphExport.export(bb, method, objectNames));
            }
            start = step("graphs", start);
            // Written graph by graph: the graphs of a framework are longer than a String can be (2^31 characters).
            write(irPath, w -> {
                w.write("{\n");
                facts.writeTo(w);
                w.write(",\n  \"graphs\": ");
                GraphExport.writeJson(w, graphs, 1);
                w.write("\n}\n");
            });
            out.println();
            out.println("wrote " + graphs.size() + " graphs to " + irPath);
        }
        step("write", start);
    }

    /**
     * Adds the time since {@code start} to a step of the export, and gives the time it ends at.
     */
    static long step(String name, long start) {
        long now = System.nanoTime();
        STEP_NANOS.merge(name, now - start, Long::sum);
        return now;
    }

    /**
     * The facts of one reachable method whose flows the analysis made, under the method's name.
     */
    private static Facts collect(PointsToAnalysis bb, PointsToAnalysisMethod ptm, boolean compiled) {
        AnalysisMethod method = ptm;
        Facts f = new Facts();
        String name = GraphExport.methodKey(method);
        if (isProgramClass(method.getDeclaringClass().toJavaName(true))) {
            f.program.add(name);
        }

        StructuredGraph body;
        try {
            body = GraphExport.analysisGraph(bb, ptm);
        } catch (VirtualMachineError e) {
            throw e;
        } catch (Throwable t) {
            // Decoding a graph again after the analysis fails where a plugin only runs before
            // Native Image seals its registries: then the method may touch anything.
            add(f.unknown, name, "no graph after the analysis (" + t.getClass().getSimpleName() + ")");
            body = null;
        }
        if (body != null) {
            f.analysed.add(name);
            // An invoke inlined before the analysis has its flow at the outermost call
            // site, which more than one invoke may share: they are told apart by target.
            Map<String, List<InvokeTypeFlow>> flows = GraphExport.flows(ptm);
            // What each access's receiver may point to, for the program's
            // own methods: a field or array access elsewhere may touch any
            // object with the field or of the kind.
            GraphExport.PointsTo pointsTo = f.program.contains(name) ? new GraphExport.PointsTo(bb, ptm) : null;
            GraphExport.PointsTo synchronizedOn = pointsTo; // made on the first synchronization of a method outside the program
            for (Node n : body.getNodes()) {
                String at = " at bci " + (n instanceof ValueNode value ? GraphExport.bci(value) : -1);
                ValueNode[] unsafeStore = unsafeStore(n);
                if (unsafeStore != null) {
                    // The analysis, when it is conservative about unsafe access, models nothing of these stores.
                    synchronizedOn = synchronizedOn != null ? synchronizedOn : new GraphExport.PointsTo(bb, ptm);
                    f.unsafeStores.add(new ThreadEscape.UnsafeStore(ptm, name + at, synchronizedOn.flowsOf(unsafeStore[0]), synchronizedOn.flowsOf(unsafeStore[1]),
                                    (AnalysisType) StampTool.typeOrNull(unsafeStore[1], bb.getMetaAccess())));
                }
                if (n instanceof AccessFieldNode access) {
                    String field = GraphExport.fieldName(access.field());
                    add(access instanceof LoadFieldNode ? f.reads : f.writes, name, field);
                    if (pointsTo != null) {
                        addAccess(f.accesses, name, access instanceof LoadFieldNode ? "read" : "write", field, pointsTo.receivers(access), access);
                    }
                    if (access.ordersMemoryAccesses()) {
                        // A volatile read acquires, a volatile write releases.
                        String what = "volatile " + (access instanceof LoadFieldNode ? "read of " : "write of ") + field + at;
                        add(access instanceof LoadFieldNode ? f.acquires : f.releases, name, what);
                        synchronizedOn = synchronizedOn != null ? synchronizedOn : new GraphExport.PointsTo(bb, ptm);
                        putSite(f.locks.computeIfAbsent(name, k -> new TreeMap<>()), what, synchronizedOn.receivers(access));
                    }
                } else if (n instanceof AccessIndexedNode access) {
                    add(access instanceof LoadIndexedNode ? f.reads : f.writes, name, GraphExport.arrayPartition(access.elementKind()));
                    if (pointsTo != null) {
                        addAccess(f.accesses, name, access instanceof LoadIndexedNode ? "read" : "write", GraphExport.arrayPartition(access.elementKind()), pointsTo.receivers(access), access);
                    }
                } else if (n instanceof BasicArrayCopyNode copy && copy.getElementKind() != null) {
                    add(f.reads, name, GraphExport.arrayPartition(copy.getElementKind()));
                    add(f.writes, name, GraphExport.arrayPartition(copy.getElementKind()));
                    if (pointsTo != null) {
                        addAccess(f.accesses, name, "read", GraphExport.arrayPartition(copy.getElementKind()), pointsTo.objects(copy.getSource()), copy);
                        addAccess(f.accesses, name, "write", GraphExport.arrayPartition(copy.getElementKind()), pointsTo.objects(copy.getDestination()), copy);
                    }
                } else if (n instanceof BasicArrayCopyNode) {
                    // An element kind Graal can't tell, so it says the copy kills anything.
                    // System.arraycopy writes the elements of an array, of some kind, and
                    // never a field.
                    for (JavaKind kind : List.of(JavaKind.Byte, JavaKind.Char, JavaKind.Short, JavaKind.Int, JavaKind.Long, JavaKind.Float, JavaKind.Double, JavaKind.Object)) {
                        add(f.reads, name, GraphExport.arrayPartition(kind));
                        add(f.writes, name, GraphExport.arrayPartition(kind));
                    }
                } else if (n instanceof AbstractNewObjectNode || n instanceof CommitAllocationNode) {
                    f.allocates.add(name);
                } else if (n instanceof ObjectClone) {
                    // Graal says a clone kills anything; it writes the object it makes, which
                    // no caller can have read, and reads all of the one it copies.
                    f.allocates.add(name);
                    add(f.unknownReads, name, n.getClass().getSimpleName() + at);
                } else if (n instanceof Invoke invoke) {
                    if (invoke.callTarget() != null && invoke.getTargetMethod() != null && isMonitorQuery(invoke.getTargetMethod()) && !invoke.callTarget().arguments().isEmpty()) {
                        synchronizedOn = synchronizedOn != null ? synchronizedOn : new GraphExport.PointsTo(bb, ptm);
                        putSite(f.waits.computeIfAbsent(name, k -> new TreeMap<>()), invoke.getTargetMethod().getName() + at, synchronizedOn.objects(invoke.callTarget().arguments().get(0)));
                    }
                    // No flow, a disabled one or one without callees: the analysis found no target.
                    List<InvokeTypeFlow> found = flows.get(GraphExport.flowKey(invoke));
                    String why = found == null ? "no flow"
                                    : found.stream().noneMatch(InvokeTypeFlow::isFlowEnabled) ? "disabled"
                                                    : found.stream().allMatch(flow -> flow.getOriginalCallees().isEmpty()) ? "no callees" : null;
                    if (why != null) {
                        add(compiled && found != null ? f.dead : f.unresolved, name, GraphExport.methodKey(invoke.getTargetMethod()) + at + " (" + why + ")");
                    }
                    if (found == null && invoke.callTarget() != null) {
                        // Code the analysis can't see, a call through a function pointer: it may keep every object it is given.
                        synchronizedOn = synchronizedOn != null ? synchronizedOn : new GraphExport.PointsTo(bb, ptm);
                        List<List<TypeFlow<?>>> arguments = new ArrayList<>();
                        for (ValueNode argument : invoke.callTarget().arguments()) {
                            if (argument.getStackKind() == JavaKind.Object) {
                                arguments.add(synchronizedOn.flowsOf(argument));
                            }
                        }
                        f.opaqueCalls.add(new ThreadEscape.OpaqueCall(ptm, name + at, arguments));
                    }
                } else if (n instanceof FinalFieldBarrierNode && ptm.isConstructor()) {
                    // Ordered by the reference: the translation has a constructor
                    // return its receiver, and every later use take that.
                } else if ((MemoryKill.isMemoryKill(n) || n instanceof MemoryAccess) && !isBookkeeping(n)) {
                    effects(n, name, n.getClass().getSimpleName() + at, f.reads, f.writes, f.allocates, f.vmWrites, f.unknown, f.unknownReads, f.acquires, f.releases);
                    if (n instanceof AccessMonitorNode monitor) {
                        synchronizedOn = synchronizedOn != null ? synchronizedOn : new GraphExport.PointsTo(bb, ptm);
                        putSite(f.locks.computeIfAbsent(name, k -> new TreeMap<>()), n.getClass().getSimpleName() + at, synchronizedOn.objects(monitor.object()));
                    }
                }
            }
        }
        MethodFlowsGraph graph = ptm.getTypeFlow().getMethodFlowsGraph();
        for (TypeFlow<?> flow : graph.flows()) {
            if (flow instanceof AccessFieldTypeFlow access) {
                AnalysisField field = access.field();
                String fq = GraphExport.fieldName(field);
                if (flow instanceof LoadFieldTypeFlow) {
                    f.reads.computeIfAbsent(name, k -> new TreeSet<>()).add(fq);
                } else if (flow instanceof StoreFieldTypeFlow) {
                    f.writes.computeIfAbsent(name, k -> new TreeSet<>()).add(fq);
                }
            }
        }

        // The call graph, points-to resolved: a virtual call yields every
        // target the analysis considers possible, not just the declared one. 
        for (InvokeTypeFlow invoke : graph.getInvokes()) {
            for (AnalysisMethod callee : invoke.getOriginalCallees()) {
                String target = GraphExport.methodKey(callee);
                f.callees.computeIfAbsent(name, k -> new TreeSet<>()).add(target);
            }
        }
        return f;
    }

    /** How many sites had the label of another site of their method, and had their objects merged with it. */
    private static final java.util.concurrent.atomic.AtomicInteger SITE_LABEL_COLLISIONS = new java.util.concurrent.atomic.AtomicInteger();

    /**
     * Records the objects a lock, a volatile access or a wait may be on, under its label. The label names
     * the node's innermost bytecode index only, so two nodes of one graph can have the same one: a
     * method's own lock and one inlined into it before the analysis, both at index 0. Both are kept, and
     * the objects are unknown if they are for either, so that a site is judged by everything that shares
     * its label: a lock on shared objects must not be judged by the thread-local ones next to it.
     */
    @SuppressWarnings("unchecked")
    private static void putSite(TreeMap<String, Object> sites, String label, List<String> receivers) {
        if (!sites.containsKey(label)) {
            sites.put(label, receivers);
            return;
        }
        SITE_LABEL_COLLISIONS.incrementAndGet();
        Object before = sites.get(label);
        if (before == null || receivers == null) {
            sites.put(label, null);
            return;
        }
        TreeSet<String> both = new TreeSet<>((List<String>) before);
        both.addAll(receivers);
        sites.put(label, new ArrayList<>(both));
    }

    /** Whether a call asks about a monitor: waits or notifies on an object, or asks whether the thread holds it. */
    private static boolean isMonitorQuery(jdk.vm.ci.meta.ResolvedJavaMethod method) {
        String owner = method.getDeclaringClass().toJavaName(true);
        String name = method.getName();
        return owner.equals("java.lang.Object") && (name.equals("wait") || name.equals("wait0") || name.equals("notify") || name.equals("notifyAll")) ||
                        owner.equals("java.lang.Thread") && name.equals("holdsLock");
    }

    /**
     * The object and the value of a node that stores a reference at an offset: an unsafe put, a
     * compare-and-swap, an exchange; null for any other node.
     */
    private static ValueNode[] unsafeStore(Node n) {
        if (n instanceof RawStoreNode store && store.value().getStackKind() == JavaKind.Object) {
            return new ValueNode[]{store.object(), store.value()};
        } else if (n instanceof AbstractUnsafeCompareAndSwapNode swap && swap.newValue().getStackKind() == JavaKind.Object) {
            return new ValueNode[]{swap.object(), swap.newValue()};
        } else if (n instanceof AtomicReadAndWriteNode swap && swap.newValue().getStackKind() == JavaKind.Object) {
            return new ValueNode[]{swap.object(), swap.newValue()};
        }
        return null;
    }

    /**
     * The facts of one method, or of all of them once merged, each under the method's name.
     */
    private static final class Facts {
        final TreeMap<String, TreeSet<String>> reads = new TreeMap<>();
        final TreeMap<String, TreeSet<String>> writes = new TreeMap<>();
        final TreeMap<String, TreeSet<String>> callees = new TreeMap<>();
        final TreeSet<String> analysed = new TreeSet<>();
        final TreeSet<String> program = new TreeSet<>();
        final TreeSet<String> allocates = new TreeSet<>();
        final TreeMap<String, TreeSet<String>> unknown = new TreeMap<>();
        final TreeMap<String, TreeSet<String>> acquires = new TreeMap<>();
        final TreeMap<String, TreeSet<String>> releases = new TreeMap<>();
        // For each method, the objects each of its acquires and releases synchronizes on, where
        // the analysis can name them: a lock's object, a volatile field's receivers.
        final TreeMap<String, TreeMap<String, Object>> locks = new TreeMap<>();
        // For each method, the objects its calls to wait, notify, notifyAll and holdsLock are on, where the
        // analysis can name them: an object that is waited on needs its monitor held.
        final TreeMap<String, TreeMap<String, Object>> waits = new TreeMap<>();
        final TreeMap<String, TreeSet<String>> unresolved = new TreeMap<>();
        final TreeMap<String, TreeSet<String>> accesses = new TreeMap<>();
        final TreeMap<String, TreeSet<String>> vmWrites = new TreeMap<>();
        final TreeMap<String, TreeSet<String>> unknownReads = new TreeMap<>();
        final TreeMap<String, TreeSet<String>> dead = new TreeMap<>();
        final List<ThreadEscape.UnsafeStore> unsafeStores = new ArrayList<>();
        final List<ThreadEscape.OpaqueCall> opaqueCalls = new ArrayList<>();

        void merge(Facts other) {
            for (var pair : List.of(List.of(reads, other.reads), List.of(writes, other.writes), List.of(callees, other.callees),
                            List.of(unknown, other.unknown), List.of(acquires, other.acquires), List.of(releases, other.releases),
                            List.of(unresolved, other.unresolved), List.of(accesses, other.accesses), List.of(vmWrites, other.vmWrites),
                            List.of(unknownReads, other.unknownReads), List.of(dead, other.dead))) {
                pair.get(1).forEach((m, facts) -> pair.get(0).computeIfAbsent(m, k -> new TreeSet<>()).addAll(facts));
            }
            analysed.addAll(other.analysed);
            program.addAll(other.program);
            allocates.addAll(other.allocates);
            unsafeStores.addAll(other.unsafeStores);
            opaqueCalls.addAll(other.opaqueCalls);
            other.locks.forEach((m, sites) -> locks.computeIfAbsent(m, k -> new TreeMap<>()).putAll(sites));
            other.waits.forEach((m, sites) -> waits.computeIfAbsent(m, k -> new TreeMap<>()).putAll(sites));
        }
    }

    private static void factsJson(java.io.Writer out, Set<String> methods,
                    TreeMap<String, TreeSet<String>> reads,
                    TreeMap<String, TreeSet<String>> writes,
                    TreeMap<String, TreeSet<String>> callees,
                    Set<String> allocates,
                    TreeMap<String, TreeSet<String>> unknown,
                    TreeMap<String, TreeSet<String>> acquires,
                    TreeMap<String, TreeSet<String>> releases,
                    TreeMap<String, TreeMap<String, Object>> locks,
                    TreeMap<String, TreeMap<String, Object>> waits,
                    TreeMap<String, TreeSet<String>> unresolved,
                    TreeMap<String, TreeSet<String>> accesses,
                    TreeMap<String, boolean[]> fields,
                    TreeMap<String, TreeSet<String>> vmWrites,
                    TreeMap<String, TreeSet<String>> unknownReads,
                    TreeMap<String, TreeSet<String>> dead) throws java.io.IOException {

        Set<String> allMethods = new TreeSet<>(methods);
        allMethods.addAll(callees.keySet());
        StringBuilder sb = new StringBuilder();
        out.write("  \"methods\": {\n");
        boolean firstMethod = true;

        for (String m : allMethods) {
            if (!firstMethod) {
                out.write(",\n");
            }
            firstMethod = false;
            sb.setLength(0);
            sb.append("    \"").append(m).append("\": {")
                            .append("\"reads\": ").append(jsonArray(reads.get(m)))
                            .append(", \"writes\": ").append(jsonArray(writes.get(m)))
                            .append(", \"callees\": ").append(jsonArray(callees.get(m)))
                            .append(", \"allocates\": ").append(allocates.contains(m))
                            .append(", \"unknown\": ").append(jsonArray(unknown.get(m)))
                            .append(", \"acquires\": ").append(jsonArray(acquires.get(m)))
                            .append(", \"releases\": ").append(jsonArray(releases.get(m)))
                            .append(", \"unresolved\": ").append(jsonArray(unresolved.get(m)))
                            .append(", \"vmWrites\": ").append(jsonArray(vmWrites.get(m)))
                            .append(", \"unknownReads\": ").append(jsonArray(unknownReads.get(m)))
                            .append(", \"dead\": ").append(jsonArray(dead.get(m)));
            if (accesses.containsKey(m)) {
                sb.append(", \"accesses\": [").append(String.join(", ", accesses.get(m))).append("]");
            }
            if (locks.containsKey(m)) {
                sb.append(", \"locks\": ").append(GraphExport.toJson(locks.get(m), 3));
            }
            if (waits.containsKey(m)) {
                sb.append(", \"waits\": ").append(GraphExport.toJson(waits.get(m), 3));
            }
            sb.append("}");
            out.append(sb);
        }

        out.write("\n  },\n  \"fields\": {\n");
        boolean firstField = true;

        for (var e : fields.entrySet()) {
            if (!firstField) {
                out.write(",\n");
            }
            firstField = false;
            sb.setLength(0);
            sb.append("    \"").append(e.getKey()).append("\": {")
                            .append("\"read\": ").append(e.getValue()[0])
                            .append(", \"written\": ").append(e.getValue()[1])
                            .append("}");
            out.append(sb);
        }
        out.write("\n  }");
    }

    /**
     * Nodes that kill or read memory for Graal's bookkeeping only: the state at
     * the method's start and at a handler's, the creation of an exception on a
     * path that throws, and an array's length, which never changes.
     */
    private static boolean isBookkeeping(Node n) {
        return n instanceof StartNode || n instanceof ExceptionObjectNode || n instanceof BytecodeExceptionNode || n instanceof ArrayLengthNode;
    }

    /**
     * A memory node the facts don't model one by one, by what Graal says it does: the locations
     * it kills, and the one it reads. Synchronization (an ordered access, a lock, a fence, an
     * atomic update) is an acquire, a release or both, which Graal says kills any location; any
     * other kill of any location may touch anything; a read of any location may read anything,
     * which matters to the tokens but not to what a call may write.
     */
    private static void effects(Node n, String method, String what, TreeMap<String, TreeSet<String>> reads, TreeMap<String, TreeSet<String>> writes,
                    Set<String> allocates, TreeMap<String, TreeSet<String>> vmWrites, TreeMap<String, TreeSet<String>> unknown,
                    TreeMap<String, TreeSet<String>> unknownReads, TreeMap<String, TreeSet<String>> acquires, TreeMap<String, TreeSet<String>> releases) {
        Synchronization synchronization = synchronization(n);
        if (synchronization != null) {
            if (synchronization.acquires()) {
                add(acquires, method, what);
            }
            if (synchronization.releases()) {
                add(releases, method, what);
            }
            return;
        }
        if (MemoryKill.isMemoryKill(n)) {
            LocationIdentity[] killed = MemoryKill.isMultiMemoryKill(n) ? MemoryKill.asMultiMemoryKill(n).getKilledLocationIdentities()
                            : new LocationIdentity[]{MemoryKill.asSingleMemoryKill(n).getKilledLocationIdentity()};
            if (java.util.Arrays.stream(killed).anyMatch(LocationIdentity::isAny)) {
                add(unknown, method, what);
                return;
            }
            for (LocationIdentity killedLocation : killed) {
                if (killedLocation.isInit()) {
                    allocates.add(method);
                } else if (location(killedLocation) instanceof String written) {
                    add(written.startsWith("vm:") ? vmWrites : writes, method, written);
                }
            }
        }
        if (n instanceof MemoryAccess access) {
            LocationIdentity read = access.getLocationIdentity();
            if (read.isAny()) {
                add(unknownReads, method, what);
            } else if (!read.isInit() && location(read) instanceof String location && !location.startsWith("vm:")) {
                add(reads, method, location);
            }
        }
    }

    /**
     * What a node that synchronizes does, by the Java memory model. After an acquire, this thread
     * may see what other threads wrote before their release; after a release, other threads may
     * see what this one wrote before it.
     */
    private record Synchronization(boolean acquires, boolean releases) {
        static final Synchronization ACQUIRE = new Synchronization(true, false);
        static final Synchronization RELEASE = new Synchronization(false, true);
        static final Synchronization BOTH = new Synchronization(true, true);
    }

    /**
     * Whether a node synchronizes, and how; null if it doesn't. Entering a lock acquires and
     * leaving it releases. An ordered load acquires and an ordered store releases: a load can't
     * show this thread's writes to others, nor a store others' writes to this one. An opaque
     * access does neither, which counting it as one only overstates. An atomic update, a fence,
     * and anything else that orders memory do both.
     */
    private static Synchronization synchronization(Node n) {
        if (n instanceof MonitorEnter) {
            return Synchronization.ACQUIRE;
        }
        if (n instanceof MonitorExit) {
            return Synchronization.RELEASE;
        }
        if (n instanceof OrderedMemoryAccess ordered && ordered.ordersMemoryAccesses()) {
            if (n instanceof LoadFieldNode || n instanceof ReadNode || n instanceof RawLoadNode) {
                return Synchronization.ACQUIRE;
            }
            if (n instanceof StoreFieldNode || n instanceof AbstractWriteNode || n instanceof RawStoreNode) {
                return Synchronization.RELEASE;
            }
            return Synchronization.BOTH;
        }
        String kind = n.getClass().getSimpleName();
        boolean synchronizes = kind.contains("Monitor") || kind.contains("CompareAndSwap") || kind.contains("CompareAndExchange") || kind.contains("Atomic") ||
                        kind.contains("Membar") || kind.contains("Fence");
        return synchronizes ? Synchronization.BOTH : null;
    }

    /** Where a node is, as the exported facts and the decisions about them name it: method:bci, then each caller. */
    public static String position(BytecodePosition position) {
        return GraphExport.PointsTo.site(position);
    }

    /**
     * A location as the facts name it: a field, an array kind, or vm: and the name of one of the
     * VM's own, such as vm:TLAB.top. Null for one that never changes.
     */
    private static String location(LocationIdentity location) {
        if (location.isImmutable()) {
            return null;
        }
        if (location instanceof FieldLocationIdentity field) {
            return GraphExport.fieldName(field.getField());
        }
        if (NamedLocationIdentity.isArrayLocation(location)) {
            for (JavaKind kind : JavaKind.values()) {
                if (NamedLocationIdentity.getArrayLocation(kind) == location) {
                    return GraphExport.arrayPartition(kind);
                }
            }
        }
        String name = "vm:" + location;
        VM_LOCATIONS.put(name, location);
        return name;
    }

    private static void add(TreeMap<String, TreeSet<String>> facts, String method, String fact) {
        facts.computeIfAbsent(method, k -> new TreeSet<>()).add(fact);
    }

    /**
     * A field or array access, where it is, and the objects its receiver may point
     * to, null when the analysis can't say: {"kind": "read", "field": "Examples$Counter.value",
     * "receivers": ["Examples$Counter@Examples.main([Ljava/lang/String;)V:9"],
     * "at": "Examples.length(LExamples$Link;)I:5"}.
     */
    private static void addAccess(TreeMap<String, TreeSet<String>> accesses, String method, String kind, String field, List<String> receivers, Node node) {
        Map<String, Object> access = new java.util.LinkedHashMap<>();
        access.put("kind", kind);
        access.put("field", field);
        access.put("receivers", receivers);
        access.put("at", GraphExport.PointsTo.site(node instanceof ValueNode value ? value.getNodeSourcePosition() : null));
        add(accesses, method, GraphExport.toJson(access, 2));
    }

    /**
     * Text that is written to a file piece by piece, because a large export is longer than a
     * String can be.
     */
    private interface Content {
        void writeTo(java.io.Writer out) throws java.io.IOException;
    }

    private static void write(String path, Content content) {
        try {
            java.nio.file.Path out = java.nio.file.Path.of(path).toAbsolutePath();
            java.nio.file.Path parent = out.getParent();
            if (parent != null) {
                java.nio.file.Files.createDirectories(parent);
            }
            try (java.io.Writer writer = java.nio.file.Files.newBufferedWriter(out)) {
                content.writeTo(writer);
            }
        } catch (java.io.IOException e) {
            throw new RuntimeException("could not write " + path, e);
        }
    }

    private static String jsonArray(Set<String> values) {
        return GraphExport.toJson(values == null ? List.of() : new ArrayList<>(values), 0);
    }
}
