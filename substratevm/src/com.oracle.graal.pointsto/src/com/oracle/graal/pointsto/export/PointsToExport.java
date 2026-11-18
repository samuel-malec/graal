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

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.Writer;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Consumer;
import java.util.function.Function;

import org.graalvm.word.LocationIdentity;

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
import jdk.graal.compiler.nodes.extended.BytecodeExceptionNode;
import jdk.graal.compiler.nodes.extended.MonitorEnter;
import jdk.graal.compiler.nodes.extended.MonitorExit;
import jdk.graal.compiler.nodes.extended.RawLoadNode;
import jdk.graal.compiler.nodes.extended.RawStoreNode;
import jdk.graal.compiler.nodes.java.AbstractNewObjectNode;
import jdk.graal.compiler.nodes.java.AbstractUnsafeCompareAndSwapNode;
import jdk.graal.compiler.nodes.java.AccessFieldNode;
import jdk.graal.compiler.nodes.java.AccessIndexedNode;
import jdk.graal.compiler.nodes.java.AccessMonitorNode;
import jdk.graal.compiler.nodes.java.ArrayLengthNode;
import jdk.graal.compiler.nodes.java.AtomicReadAndWriteNode;
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
import jdk.graal.compiler.nodes.type.StampTool;
import jdk.graal.compiler.nodes.virtual.CommitAllocationNode;
import jdk.graal.compiler.replacements.nodes.BasicArrayCopyNode;
import jdk.graal.compiler.replacements.nodes.ObjectClone;
import jdk.vm.ci.code.BytecodePosition;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;

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

    /** What each method's graph said when the analysis built its flows from it; null while nothing records. */
    private static volatile Map<AnalysisMethod, Recorded> recorded;

    /** How long recording took, summed over the analysis' threads. */
    private static final AtomicLong RECORDING_NANOS = new AtomicLong();

    /**
     * Has the analysis keep what each method's graph says, as it builds the method's flows from it,
     * for an export of kill sets without thread escape: then that export decodes and optimizes no
     * graph again after the analysis, which is most of what its facts cost. A graph the analysis
     * builds again replaces what the one before said, and the export decodes again the graph of a
     * method without one, as it does without recording. Call before the analysis runs.
     */
    public static void recordDuringAnalysis(PointsToAnalysis bb) {
        Map<AnalysisMethod, Recorded> graphs = new ConcurrentHashMap<>();
        RECORDING_NANOS.set(0);
        recorded = graphs;
        bb.setGraphListener((method, graph) -> {
            long start = System.nanoTime();
            Recorded found = new Recorded();
            try {
                for (Node n : graph.getNodes()) {
                    scan(n, method.isConstructor(), found);
                }
                graphs.put(method, found);
            } catch (RuntimeException e) {
                // Not the analysis' to fail: the export decodes the graph again, and finds out.
                graphs.remove(method);
            }
            RECORDING_NANOS.addAndGet(System.nanoTime() - start);
        });
    }

    /** Ends what {@link #recordDuringAnalysis} started, and forgets what it recorded. */
    public static void stopRecording(PointsToAnalysis bb) {
        bb.setGraphListener(null);
        recorded = null;
    }

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

    /**
     * How well the facts describe a method: not at all, with an effect or a call they can't name
     * that may store a reference, or whole.
     */
    private static Function<AnalysisMethod, ThreadEscape.Described> describedBy(Set<String> analysed, TreeMap<String, TreeSet<String>> unknown) {
        return method -> {
            String key = GraphExport.methodKey(method);
            if (!analysed.contains(key)) {
                return ThreadEscape.Described.NOTHING;
            }
            TreeSet<String> effects = unknown.get(key);
            return (effects != null && effects.stream().anyMatch(effect -> !STORES_NO_REFERENCE.contains(effect.replaceFirst(" at bci.*", ""))))
                            ? ThreadEscape.Described.UNKNOWN_EFFECT
                            : ThreadEscape.Described.WHOLE;
        };
    }

    /**
     * The assumptions {@code -Dsideeffects.assumptions} names, comma-separated; none without it.
     * See {@link #export(PointsToAnalysis, AnalysisUniverse, String, String, PrintStream, boolean, String, boolean, Set)}.
     */
    public static Set<String> defaultAssumptions() {
        String names = System.getProperty("sideeffects.assumptions", "");
        return names.isEmpty() ? Set.of() : Set.of(names.split(","));
    }

    /** Packages treated as "not the program under analysis" by default. */
    private static final String[] PLATFORM = {
                    "java.", "javax.", "jdk.", "sun.", "com.sun.",
                    "com.oracle.", "org.graalvm.",
                    "org.ietf.", "org.jcp.", "org.w3c.", "org.xml.",
    };

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
     * Exports what the analysis knows, as {@link #export(PointsToAnalysis, AnalysisUniverse, String,
     * String, PrintStream, boolean, String, boolean, Set)} does, with thread escape and the
     * assumptions {@code -Dsideeffects.assumptions} names.
     */
    public static void export(PointsToAnalysis bb, AnalysisUniverse universe, String jsonPath, String irPath, PrintStream report, boolean compiled, String programPrefix) {
        export(bb, universe, jsonPath, irPath, report, compiled, programPrefix, true, defaultAssumptions());
    }

    /**
     * Exports the facts of every reachable method, and the graphs of the program's, from an
     * analysis that has run: the standalone analyzer's, or Native Image's own, from a feature.
     * An empty path skips that file; the reports go to {@code report}, null for none.
     * {@code compiled} says the graphs are about to be compiled into an image, so calls the
     * analysis found no target for never happen; {@code programPrefix} names the program, as
     * {@link #isProgramClass(String, String)} takes it.
     * <p>
     * With {@code threadEscape}, the export works out which objects other threads can reach, and
     * records the locks and volatile accesses to judge them by. Without it, the facts say only
     * that a method acquires or releases, and no list of shared objects: the tool then counts every
     * acquire and release as ordering this thread with another, which is the sound answer without
     * that knowledge. {@code assumptions} are those thread escape makes on top of what the
     * analysis shows, by name: {@code thread-confined}, {@code vm-fields}, {@code vm-code},
     * {@code handler-references} and {@code entry-points}, which {@link ThreadEscape} describes;
     * none makes the answer follow from the analysis alone.
     */
    public static void export(PointsToAnalysis bb, AnalysisUniverse universe, String jsonPath, String irPath, PrintStream report, boolean compiled, String programPrefix,
                    boolean threadEscape, Set<String> assumptions) {
        export(bb, universe, jsonPath, irPath, report, compiled, programPrefix, threadEscape, assumptions, false);
    }

    /**
     * As {@link #export(PointsToAnalysis, AnalysisUniverse, String, String, PrintStream, boolean, String, boolean, Set)},
     * and with {@code killSets} also works out from the same facts what each method, with
     * everything it calls, may write, as the tool's effects.kills does with partitions by field:
     * the lines the tool writes to kills.txt ({@link KillSetComputation}). With both paths empty,
     * nothing is written and the facts are collected for the kill sets alone. Without thread escape,
     * and once {@link #recordDuringAnalysis} has had the analysis record its graphs, the kill sets
     * are worked out from those, and the graphs are decoded again only for what is written; a
     * method whose graph doesn't decode again is written with its recorded graph's facts, so the
     * tool and the build have the same facts of it. Null without {@code killSets}.
     */
    public static List<String> export(PointsToAnalysis bb, AnalysisUniverse universe, String jsonPath, String irPath, PrintStream report, boolean compiled, String programPrefix,
                    boolean threadEscape, Set<String> assumptions, boolean killSets) {
        STEP_NANOS.clear();
        SITE_LABEL_COLLISIONS.set(0);
        NOT_DECODED_AGAIN.set(0);
        long start = System.nanoTime();
        PrintStream out = report != null ? report : new PrintStream(OutputStream.nullOutputStream());
        // Before any name is made: names are keys, and the keys decide the order things are written in.
        GraphExport.nameHiddenClasses(universe.getTypes(), out);
        // Thread escape needs the objects of the nodes, which a recorded graph doesn't keep.
        Map<AnalysisMethod, Recorded> recordedGraphs = killSets && !threadEscape ? recorded : null;
        boolean whole = recordedGraphs == null || !jsonPath.isEmpty() || !irPath.isEmpty() || report != null;
        Facts found = whole ? facts(universe, method -> collect(bb, method, compiled, threadEscape, programPrefix, recordedGraphs)) : null;
        if (whole) {
            if (SITE_LABEL_COLLISIONS.get() > 0) {
                diagnostics().println("SIDEEFFECT " + SITE_LABEL_COLLISIONS.get() + " locks, volatile accesses or waits had the label of another site in their method; their objects were merged");
            }
            if (NOT_DECODED_AGAIN.get() > 0) {
                diagnostics().println("SIDEEFFECT " + NOT_DECODED_AGAIN.get() + " methods had no graph when decoded again after the analysis; their facts are from the graphs the analysis recorded");
            }
            start = step("facts", start);
        }
        Facts forKillSets = recordedGraphs == null ? found
                        : facts(universe, method -> recordedGraphs.get(method) instanceof Recorded graph ? recalled(method, graph, compiled)
                                        : collect(bb, method, compiled, threadEscape, programPrefix, recordedGraphs));
        if (recordedGraphs != null) {
            STEP_NANOS.put("recording (summed over the analysis' threads)", RECORDING_NANOS.get());
            start = step("recorded facts", start);
        }
        TreeMap<String, boolean[]> fields = whole ? programFields(universe, programPrefix) : null;
        if (report != null) {
            // Formatted for no one, the report costs PetClinic's build two seconds.
            printReport(out, found, fields, programPrefix);
        }
        start = step("report", start);
        TreeSet<String> shared = threadEscape ? ThreadEscape.sharedObjects(bb, universe, describedBy(found.analysed, found.unknown), compiled, assumptions, found.unsafeStores, found.opaqueCalls)
                        : null;
        start = step("thread escape", start);
        List<String> kills = null;
        if (killSets) {
            kills = KillSetComputation.lines(forKillSets, shared);
            start = step("kill sets", start);
        }
        // For evaluation: what each assumption adds, from one analysis.
        Map<String, TreeSet<String>> byAssumptions = threadEscape && System.getProperty("sideeffects.assumptionLayers") != null
                        ? sharedByAssumptions(bb, universe, found, compiled)
                        : new TreeMap<>();
        // Written method by method, and the shared objects one by one: with allocation sites the facts and the shared objects are each longer than
        // a String can be (2^31 characters).
        Content facts = w -> {
            found.writeJson(w, fields);
            if (shared != null) {
                w.write(",\n  \"sharedObjects\": ");
                GraphExport.writeJson(w, shared);
            }
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
            List<PointsToAnalysisMethod> methods = programMethods(universe, programPrefix);
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
        return kills;
    }

    /**
     * The objects another thread may reach under each set of assumptions, from one analysis: none,
     * then the assumptions added one after the other, and the two the lock elision uses.
     */
    private static Map<String, TreeSet<String>> sharedByAssumptions(PointsToAnalysis bb, AnalysisUniverse universe, Facts found, boolean compiled) {
        Map<String, TreeSet<String>> byAssumptions = new TreeMap<>();
        for (String layer : List.of("", "thread-confined", "thread-confined,vm-fields", "thread-confined,vm-fields,vm-code", "thread-confined,vm-fields,vm-code,handler-references",
                        "thread-confined,vm-fields,vm-code,handler-references,entry-points", "vm-code,entry-points")) {
            byAssumptions.put(layer.isEmpty() ? "none" : layer, ThreadEscape.sharedObjects(bb, universe, describedBy(found.analysed, found.unknown), compiled,
                            layer.isEmpty() ? Set.of() : Set.of(layer.split(",")), found.unsafeStores, found.opaqueCalls));
        }
        return byAssumptions;
    }

    /**
     * The program's reachable methods whose flows the analysis made, in the order of their names and
     * descriptors: the order their graphs are written in.
     */
    private static List<PointsToAnalysisMethod> programMethods(AnalysisUniverse universe, String programPrefix) {
        List<PointsToAnalysisMethod> methods = new ArrayList<>();
        for (AnalysisMethod method : universe.getMethods()) {
            if (method.isReachable() && method instanceof PointsToAnalysisMethod ptm && ptm.getTypeFlow().flowsGraphCreated() &&
                            isProgramClass(method.getDeclaringClass().toJavaName(true), programPrefix)) {
                methods.add(ptm);
            }
        }
        methods.sort(Comparator.comparing(method -> GraphExport.methodName(method) + " " + GraphExport.stable(method.getSignature().toMethodDescriptor())));
        return methods;
    }

    /** The program's fields, and whether the analysis found each read and written. */
    private static TreeMap<String, boolean[]> programFields(AnalysisUniverse universe, String programPrefix) {
        TreeMap<String, boolean[]> fields = new TreeMap<>();
        for (AnalysisField f : universe.getFields()) {
            if (!isProgramClass(f.getDeclaringClass().toJavaName(true), programPrefix)) {
                continue;
            }
            fields.put(GraphExport.fieldName(f), new boolean[]{f.isRead(), f.isWritten()});
        }
        return fields;
    }

    /**
     * Prints, for people, what the facts say of the program's methods: the fields each reads and
     * writes, the calls between them, the program's fields, and what the facts can't name.
     */
    private static void printReport(PrintStream out, Facts found, TreeMap<String, boolean[]> fields, String programPrefix) {
        Set<String> all = new TreeSet<>();
        all.addAll(found.reads.keySet());
        all.addAll(found.writes.keySet());
        all.retainAll(found.program);

        out.println();
        out.println("=== local per-method field effects ===");
        if (all.isEmpty()) {
            out.println("  (nothing reported -- wrong -Ddump.filter, or no reachable");
            out.println("   field accesses in the analysed program?)");
        }
        for (String m : all) {
            out.printf("  %-34s reads=%-28s writes=%s%n",
                            m,
                            found.reads.getOrDefault(m, new TreeSet<>()),
                            found.writes.getOrDefault(m, new TreeSet<>()));
        }

        out.println();
        out.println("=== call graph with points-to resolved callees ===");
        for (String m : new TreeSet<>(found.callees.keySet())) {
            if (!found.program.contains(m)) {
                continue;
            }
            TreeSet<String> targets = new TreeSet<>();
            for (String t : found.callees.get(m)) {
                targets.add(isProgramClass(t.substring(0, t.lastIndexOf('.', t.indexOf('('))), programPrefix) ? t : "<platform>");
            }
            targets.remove("<platform>");
            if (!targets.isEmpty()) {
                out.printf("  %-34s -> %s%n", m, targets);
            }
        }

        out.println();
        out.println("=== reachable fields ===");
        for (var e : fields.entrySet()) {
            out.printf("  %-30s read=%-6s written=%s%n",
                            e.getKey(), e.getValue()[0], e.getValue()[1]);
        }

        out.println();
        out.println("=== synchronization, memory effects the facts can't name, and calls without a target ===");
        for (String m : found.program) {
            for (String what : found.acquires.getOrDefault(m, new TreeSet<>())) {
                out.printf("  %-34s acquire: %s%n", m, what);
            }
            for (String what : found.releases.getOrDefault(m, new TreeSet<>())) {
                out.printf("  %-34s release: %s%n", m, what);
            }
            for (String what : found.unknown.getOrDefault(m, new TreeSet<>())) {
                out.printf("  %-34s %s%n", m, what);
            }
            for (String what : found.unresolved.getOrDefault(m, new TreeSet<>())) {
                out.printf("  %-34s unresolved call to %s%n", m, what);
            }
        }
    }

    /**
     * Where the export prints its diagnostics, which scripts read from the build's log: the
     * standard error, as the builder or the standalone analyzer has it when they are printed.
     */
    static PrintStream diagnostics() {
        // Checkstyle: allow System.err (diagnostics that scripts read from the build's log)
        return System.err;
        // Checkstyle: disallow System.err
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
     * The facts of every reachable method whose flows the analysis made, as {@code collector} gives
     * each method's. Each method's facts are its own: they are collected in parallel, and merged
     * into sorted maps, so the export is the same as one made method by method.
     */
    private static Facts facts(AnalysisUniverse universe, Function<PointsToAnalysisMethod, Facts> collector) {
        Facts found = new Facts();
        universe.getMethods().parallelStream()
                        .filter(method -> method.isReachable() && method instanceof PointsToAnalysisMethod ptm && ptm.getTypeFlow().flowsGraphCreated())
                        .map(method -> collector.apply((PointsToAnalysisMethod) method))
                        .toList()
                        .forEach(found::merge);
        return found;
    }

    /**
     * The facts the kill sets need of a method, as {@link #collect} finds them, from what its graph
     * said when the analysis built the method's flows from it.
     */
    private static Facts recalled(PointsToAnalysisMethod ptm, Recorded graph, boolean compiled) {
        Facts f = new Facts();
        String name = GraphExport.methodKey(ptm);
        f.analysed.add(name);
        graph.replay(new Named(f, name, GraphExport.flows(ptm), compiled));
        flowFacts(ptm, name, f);
        return f;
    }

    /**
     * The facts of one reachable method whose flows the analysis made, under the method's name.
     * Where its graph doesn't decode again after the analysis and {@code recordedGraphs} (null
     * when nothing was recorded) has the method's, they are that graph's, as {@link #recalled}
     * finds them.
     */
    private static Facts collect(PointsToAnalysis bb, PointsToAnalysisMethod ptm, boolean compiled, boolean threadEscape, String programPrefix, Map<AnalysisMethod, Recorded> recordedGraphs) {
        return new Collector(bb, ptm, compiled, threadEscape, programPrefix).collect(recordedGraphs);
    }

    /**
     * Collects one method's facts: from its graph, decoded again after the analysis, node by node,
     * then from its flows.
     */
    private static final class Collector {
        private final PointsToAnalysis bb;
        private final PointsToAnalysisMethod ptm;
        private final boolean compiled;
        private final boolean threadEscape;
        private final String name;
        private final Facts f = new Facts();

        /**
         * The flows of the method's invokes. An invoke inlined before the analysis has its flow at
         * the outermost call site, which more than one invoke may share: they are told apart by
         * target.
         */
        private Map<String, List<InvokeTypeFlow>> flows;
        /**
         * What each access's receiver may point to, for the program's own methods only: an access
         * elsewhere may touch any object with the field or of the kind.
         */
        private GraphExport.PointsTo pointsTo;
        /** The same for synchronization and thread escape, in any method: {@link #synchronizedOn}. */
        private GraphExport.PointsTo synchronizedOn;

        Collector(PointsToAnalysis bb, PointsToAnalysisMethod ptm, boolean compiled, boolean threadEscape, String programPrefix) {
            this.bb = bb;
            this.ptm = ptm;
            this.compiled = compiled;
            this.threadEscape = threadEscape;
            this.name = GraphExport.methodKey(ptm);
            if (isProgramClass(ptm.getDeclaringClass().toJavaName(true), programPrefix)) {
                f.program.add(name);
            }
        }

        Facts collect(Map<AnalysisMethod, Recorded> recordedGraphs) {
            StructuredGraph body;
            String failure = null;
            try {
                body = GraphExport.analysisGraph(bb, ptm);
            } catch (VirtualMachineError e) {
                throw e;
            } catch (Throwable t) {
                failure = GraphExport.simpleClassName(t);
                body = null;
            }
            if (body == null && recordedGraphs != null && recordedGraphs.get(ptm) instanceof Recorded graph) {
                // The graph the analysis built the flows from, which decoding again would have given:
                // read as recalled reads it, so that what is written has the facts the kill sets have.
                NOT_DECODED_AGAIN.incrementAndGet();
                f.analysed.add(name);
                graph.replay(new Named(f, name, GraphExport.flows(ptm), compiled));
            } else if (failure != null) {
                // Decoding a graph again after the analysis fails where a plugin only runs before
                // Native Image seals its registries: then the method may touch anything.
                add(f.unknown, name, "no graph after the analysis (" + failure + ")");
            }
            if (body != null) {
                f.analysed.add(name);
                flows = GraphExport.flows(ptm);
                Named found = new Named(f, name, flows, compiled);
                pointsTo = f.program.contains(name) ? new GraphExport.PointsTo(bb, ptm) : null;
                synchronizedOn = pointsTo;
                for (Node n : body.getNodes()) {
                    scan(n, ptm.isConstructor(), found);
                    if (threadEscape || pointsTo != null) {
                        objects(n);
                    }
                }
            }
            flowFacts(ptm, name, f);
            return f;
        }

        /**
         * What the objects of a synchronization, an unsafe store or an opaque call may be: in a
         * method outside the program, made the first time one is asked for.
         */
        private GraphExport.PointsTo synchronizedOn() {
            if (synchronizedOn == null) {
                synchronizedOn = new GraphExport.PointsTo(bb, ptm);
            }
            return synchronizedOn;
        }

        /**
         * What scan leaves out of a node: the objects of its accesses and synchronization, by the
         * same kinds of node in the same order.
         */
        private void objects(Node n) {
            ValueNode[] unsafeStore = threadEscape ? unsafeStore(n) : null;
            if (unsafeStore != null) {
                // The analysis, when it is conservative about unsafe access, models nothing of these stores.
                f.unsafeStores.add(new ThreadEscape.UnsafeStore(ptm, name + at(n), synchronizedOn().flowsOf(unsafeStore[0]), synchronizedOn().flowsOf(unsafeStore[1]),
                                (AnalysisType) StampTool.typeOrNull(unsafeStore[1], bb.getMetaAccess())));
            }
            if (n instanceof AccessFieldNode access) {
                String field = GraphExport.fieldName(access.field());
                if (pointsTo != null) {
                    addAccess(f.accesses, name, access instanceof LoadFieldNode ? "read" : "write", field, pointsTo.receivers(access), access);
                }
                if (access.ordersMemoryAccesses() && threadEscape) {
                    String what = "volatile " + (access instanceof LoadFieldNode ? "read of " : "write of ") + field + at(n);
                    putSite(f.locks.computeIfAbsent(name, k -> new TreeMap<>()), what, synchronizedOn().receivers(access));
                }
            } else if (n instanceof AccessIndexedNode access) {
                if (pointsTo != null) {
                    addAccess(f.accesses, name, access instanceof LoadIndexedNode ? "read" : "write", GraphExport.arrayPartition(access.elementKind()), pointsTo.receivers(access), access);
                }
            } else if (n instanceof BasicArrayCopyNode copy) {
                if (pointsTo != null && copy.getElementKind() != null) {
                    addAccess(f.accesses, name, "read", GraphExport.arrayPartition(copy.getElementKind()), pointsTo.objects(copy.getSource()), copy);
                    addAccess(f.accesses, name, "write", GraphExport.arrayPartition(copy.getElementKind()), pointsTo.objects(copy.getDestination()), copy);
                }
            } else if (n instanceof AbstractNewObjectNode || n instanceof CommitAllocationNode || n instanceof ObjectClone) {
                // Nothing that scan doesn't find.
            } else if (n instanceof Invoke invoke) {
                invoke(invoke, at(n));
            } else if (n instanceof FinalFieldBarrierNode && ptm.isConstructor()) {
                // As in scan.
            } else if (threadEscape && n instanceof AccessMonitorNode monitor && (MemoryKill.isMemoryKill(n) || n instanceof MemoryAccess) && !isBookkeeping(n)) {
                putSite(f.locks.computeIfAbsent(name, k -> new TreeMap<>()), GraphExport.simpleClassName(n) + at(n), synchronizedOn().objects(monitor.object()));
            }
        }

        /** A call that asks about a monitor, and a call into code the analysis can't see. */
        private void invoke(Invoke invoke, String at) {
            if (threadEscape && invoke.callTarget() != null && invoke.getTargetMethod() != null && isMonitorQuery(invoke.getTargetMethod()) && !invoke.callTarget().arguments().isEmpty()) {
                putSite(f.waits.computeIfAbsent(name, k -> new TreeMap<>()), invoke.getTargetMethod().getName() + at, synchronizedOn().objects(invoke.callTarget().arguments().get(0)));
            }
            if (threadEscape && flows.get(GraphExport.flowKey(invoke)) == null && invoke.callTarget() != null) {
                // Code the analysis can't see, a call through a function pointer: it may keep every object it is given.
                GraphExport.PointsTo objects = synchronizedOn();
                List<List<TypeFlow<?>>> arguments = new ArrayList<>();
                for (ValueNode argument : invoke.callTarget().arguments()) {
                    if (argument.getStackKind() == JavaKind.Object) {
                        arguments.add(objects.flowsOf(argument));
                    }
                }
                f.opaqueCalls.add(new ThreadEscape.OpaqueCall(ptm, name + at, arguments));
            }
        }
    }

    /**
     * What the flows of a method say beyond its graph: the fields their loads and stores read and
     * write, and the call graph, points-to resolved: a virtual call yields every target the analysis
     * considers possible, not just the declared one.
     */
    private static void flowFacts(PointsToAnalysisMethod ptm, String name, Facts f) {
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

        for (InvokeTypeFlow invoke : graph.getInvokes()) {
            for (AnalysisMethod callee : invoke.getOriginalCallees()) {
                String target = GraphExport.methodKey(callee);
                f.callees.computeIfAbsent(name, k -> new TreeSet<>()).add(target);
            }
        }
    }

    /**
     * What one node of a method's graph does that the facts name: the fields and array elements it
     * reads and writes, what it allocates, the call it makes, how it synchronizes, and what another
     * node that touches memory kills and reads, by what Graal says it does. Nothing is named yet:
     * {@code found} names it, now or after the analysis.
     */
    private static void scan(Node n, boolean constructor, Scanned found) {
        if (n instanceof AccessFieldNode access) {
            found.field(access.field(), access instanceof LoadFieldNode, access.ordersMemoryAccesses(), bci(n));
        } else if (n instanceof AccessIndexedNode access) {
            found.elements(access.elementKind(), access instanceof LoadIndexedNode);
        } else if (n instanceof BasicArrayCopyNode copy && copy.getElementKind() != null) {
            found.elements(copy.getElementKind(), true);
            found.elements(copy.getElementKind(), false);
        } else if (n instanceof BasicArrayCopyNode) {
            // An element kind Graal can't tell, so it says the copy kills anything.
            // System.arraycopy writes the elements of an array, of some kind, and
            // never a field.
            for (JavaKind kind : List.of(JavaKind.Byte, JavaKind.Char, JavaKind.Short, JavaKind.Int, JavaKind.Long, JavaKind.Float, JavaKind.Double, JavaKind.Object)) {
                found.elements(kind, true);
                found.elements(kind, false);
            }
        } else if (n instanceof AbstractNewObjectNode || n instanceof CommitAllocationNode) {
            found.allocates();
        } else if (n instanceof ObjectClone) {
            // Graal says a clone kills anything; it writes the object it makes, which
            // no caller can have read, and reads all of the one it copies.
            found.allocates();
            found.unknownRead(GraphExport.simpleClassName(n), bci(n));
        } else if (n instanceof Invoke invoke) {
            found.call(GraphExport.flowBci(invoke), invoke.getTargetMethod(), bci(n));
        } else if (n instanceof FinalFieldBarrierNode && constructor) {
            // Ordered by the reference: the translation has a constructor
            // return its receiver, and every later use take that.
        } else if ((MemoryKill.isMemoryKill(n) || n instanceof MemoryAccess) && !isBookkeeping(n)) {
            effects(n, found);
        }
    }

    /** A node's innermost bytecode index, -1 for none. */
    private static int bci(Node n) {
        return n instanceof ValueNode value ? GraphExport.bci(value) : -1;
    }

    /** Where a node is, as the facts label what it does. */
    private static String at(Node n) {
        return at(bci(n));
    }

    private static String at(int bci) {
        return " at bci " + bci;
    }

    /** What {@link #scan} finds in a node, unnamed. */
    private interface Scanned {
        /** A field read or written, ordered if it is volatile. */
        void field(ResolvedJavaField field, boolean read, boolean ordered, int bci);

        /** The elements of an array of a kind read or written. */
        void elements(JavaKind kind, boolean read);

        void allocates();

        /** A call, by the outermost call site its flows have ({@link GraphExport#flowBci}) and its target. */
        void call(int flowBci, ResolvedJavaMethod target, int bci);

        /** A node, by its class's simple name, that synchronizes. */
        void synchronizes(String node, int bci, boolean acquires, boolean releases);

        /** A node that may kill any location. */
        void unknown(String node, int bci);

        void kills(LocationIdentity location);

        void reads(LocationIdentity location);

        /** A node that may read any location. */
        void unknownRead(String node, int bci);
    }

    /**
     * Names what {@link #scan} finds into the facts of one method, and checks each call against
     * the method's flows, which have to be the analysis' last.
     */
    private static final class Named implements Scanned {
        private final Facts f;
        private final String method;
        private final Map<String, List<InvokeTypeFlow>> flows;
        private final boolean compiled;

        Named(Facts f, String method, Map<String, List<InvokeTypeFlow>> flows, boolean compiled) {
            this.f = f;
            this.method = method;
            this.flows = flows;
            this.compiled = compiled;
        }

        @Override
        public void field(ResolvedJavaField field, boolean read, boolean ordered, int bci) {
            String name = GraphExport.fieldName(field);
            add(read ? f.reads : f.writes, method, name);
            if (ordered) {
                // A volatile read acquires, a volatile write releases.
                add(read ? f.acquires : f.releases, method, "volatile " + (read ? "read of " : "write of ") + name + at(bci));
            }
        }

        @Override
        public void elements(JavaKind kind, boolean read) {
            add(read ? f.reads : f.writes, method, GraphExport.arrayPartition(kind));
        }

        @Override
        public void allocates() {
            f.allocates.add(method);
        }

        @Override
        public void call(int flowBci, ResolvedJavaMethod target, int bci) {
            // No flow, a disabled one or one without callees: the analysis found no target.
            List<InvokeTypeFlow> found = flows.get(GraphExport.flowKey(flowBci, target));
            String why = found == null ? "no flow"
                            : found.stream().noneMatch(InvokeTypeFlow::isFlowEnabled) ? "disabled"
                                            : found.stream().allMatch(flow -> flow.getOriginalCallees().isEmpty()) ? "no callees" : null;
            if (why != null) {
                add(compiled && found != null ? f.dead : f.unresolved, method, GraphExport.methodKey(target) + at(bci) + " (" + why + ")");
            }
        }

        @Override
        public void synchronizes(String node, int bci, boolean acquires, boolean releases) {
            if (acquires) {
                add(f.acquires, method, node + at(bci));
            }
            if (releases) {
                add(f.releases, method, node + at(bci));
            }
        }

        @Override
        public void unknown(String node, int bci) {
            add(f.unknown, method, node + at(bci));
        }

        @Override
        public void kills(LocationIdentity location) {
            if (location.isInit()) {
                f.allocates.add(method);
            } else if (location(location) instanceof String written) {
                add(written.startsWith("vm:") ? f.vmWrites : f.writes, method, written);
            }
        }

        @Override
        public void reads(LocationIdentity location) {
            if (!location.isInit() && location(location) instanceof String read && !read.startsWith("vm:")) {
                add(f.reads, method, read);
            }
        }

        @Override
        public void unknownRead(String node, int bci) {
            add(f.unknownReads, method, node + at(bci));
        }
    }

    /**
     * What {@link #scan} found in a method's graph while the analysis had it, kept by reference
     * for after the analysis, when what it refers to can be named and the method's flows are the
     * analysis' last: what the kill sets need, so no read that does not synchronize.
     */
    private static final class Recorded implements Scanned {
        private final ArrayList<Consumer<Scanned>> found = new ArrayList<>();
        private boolean allocates;

        @Override
        public void field(ResolvedJavaField field, boolean read, boolean ordered, int bci) {
            if (!read || ordered) {
                found.add(to -> to.field(field, read, ordered, bci));
            }
        }

        @Override
        public void elements(JavaKind kind, boolean read) {
            if (!read) {
                found.add(to -> to.elements(kind, false));
            }
        }

        @Override
        public void allocates() {
            allocates = true;
        }

        @Override
        public void call(int flowBci, ResolvedJavaMethod target, int bci) {
            found.add(to -> to.call(flowBci, target, bci));
        }

        @Override
        public void synchronizes(String node, int bci, boolean acquires, boolean releases) {
            found.add(to -> to.synchronizes(node, bci, acquires, releases));
        }

        @Override
        public void unknown(String node, int bci) {
            found.add(to -> to.unknown(node, bci));
        }

        @Override
        public void kills(LocationIdentity location) {
            found.add(to -> to.kills(location));
        }

        @Override
        public void reads(LocationIdentity location) {
        }

        @Override
        public void unknownRead(String node, int bci) {
        }

        /** Gives {@code to} what was found, as scan gave it here. */
        void replay(Scanned to) {
            if (allocates) {
                to.allocates();
            }
            found.forEach(event -> event.accept(to));
        }
    }

    /** How many sites had the label of another site of their method, and had their objects merged with it. */
    private static final AtomicInteger SITE_LABEL_COLLISIONS = new AtomicInteger();

    /** How many methods had their facts written from the graph the analysis recorded, theirs not decoding again. */
    private static final AtomicInteger NOT_DECODED_AGAIN = new AtomicInteger();

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
    private static boolean isMonitorQuery(ResolvedJavaMethod method) {
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
    static final class Facts {
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

        /**
         * Writes the facts as the export's "methods" and "fields", one method and one field at a
         * time.
         */
        void writeJson(Writer out, TreeMap<String, boolean[]> fields) throws IOException {
            Set<String> allMethods = new TreeSet<>(analysed);
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
    private static void effects(Node n, Scanned found) {
        Synchronization synchronization = synchronization(n);
        if (synchronization != null) {
            found.synchronizes(GraphExport.simpleClassName(n), bci(n), synchronization.acquires(), synchronization.releases());
            return;
        }
        if (MemoryKill.isMemoryKill(n)) {
            LocationIdentity[] killed = MemoryKill.isMultiMemoryKill(n) ? MemoryKill.asMultiMemoryKill(n).getKilledLocationIdentities()
                            : new LocationIdentity[]{MemoryKill.asSingleMemoryKill(n).getKilledLocationIdentity()};
            if (Arrays.stream(killed).anyMatch(LocationIdentity::isAny)) {
                found.unknown(GraphExport.simpleClassName(n), bci(n));
                return;
            }
            for (LocationIdentity killedLocation : killed) {
                found.kills(killedLocation);
            }
        }
        if (n instanceof MemoryAccess access) {
            LocationIdentity read = access.getLocationIdentity();
            if (read.isAny()) {
                found.unknownRead(GraphExport.simpleClassName(n), bci(n));
            } else {
                found.reads(read);
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
        String kind = GraphExport.simpleClassName(n);
        boolean synchronizes = kind.contains("Monitor") || kind.contains("CompareAndSwap") || kind.contains("CompareAndExchange") || kind.contains("Atomic") ||
                        kind.contains("Membar") || kind.contains("Fence");
        return synchronizes ? Synchronization.BOTH : null;
    }

    /**
     * A method as the export names it, and so as the tool's answers do: its class, its name and its
     * descriptor, with a hidden class named by its content rather than by its address. Hidden
     * classes are named by the last export.
     */
    public static String methodKey(ResolvedJavaMethod method) {
        return GraphExport.methodKey(method);
    }

    /** A field as the export names it, a hidden class by its content: see {@link #methodKey}. */
    public static String fieldName(ResolvedJavaField field) {
        return GraphExport.fieldName(field);
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
        Map<String, Object> access = new LinkedHashMap<>();
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
        void writeTo(Writer out) throws IOException;
    }

    private static void write(String path, Content content) {
        try {
            Path out = Path.of(path).toAbsolutePath();
            Path parent = out.getParent();
            if (parent != null) {
                Files.createDirectories(parent);
            }
            try (Writer writer = Files.newBufferedWriter(out)) {
                content.writeTo(writer);
            }
        } catch (IOException e) {
            throw new RuntimeException("Could not write " + path, e);
        }
    }

    private static String jsonArray(Set<String> values) {
        return GraphExport.toJson(values == null ? List.of() : new ArrayList<>(values), 0);
    }
}
