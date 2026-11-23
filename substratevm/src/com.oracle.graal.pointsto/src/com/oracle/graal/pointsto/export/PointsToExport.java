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
 * Collects what a finished points-to analysis knows about each reachable method, and optionally
 * writes it as JSON.
 * <p>
 * For every method the export records its <em>facts</em>: the fields and array kinds it reads and
 * writes, whether it allocates, the targets of its calls, how it synchronizes, and memory effects
 * that have no name (which make it opaque). For the program's own methods it also records, for
 * each access, the objects the receiver may point to. Optionally it writes the program's
 * scheduled Graal IR as well.
 * <p>
 * The facts feed the kill sets ({@link KillSetComputation} in the builder, or the Python tool
 * {@code effects.kills} reading the JSON) and the thread-escape analysis ({@link ThreadEscape}).
 */
public final class PointsToExport {

    private PointsToExport() {
    }

    /** VM locations that appear in the facts (e.g. {@code vm:TLAB.top}), by name, so the feature can map names back to Graal locations. */
    public static final Map<String, LocationIdentity> VM_LOCATIONS = new ConcurrentHashMap<>();

    /** Time per export step in nanoseconds (facts, report, thread escape, graphs, write) for the last export. */
    public static final Map<String, Long> STEP_NANOS = new ConcurrentHashMap<>();

    /** Per method, what its graph contained when the analysis built its flows; null when not recording. */
    private static volatile Map<AnalysisMethod, Recorded> recorded;

    /** Time spent recording, summed over the analysis threads. */
    private static final AtomicLong RECORDING_NANOS = new AtomicLong();

    /**
     * Starts recording each method's graph while the analysis builds its type flows, so that the kill
     * sets can later be computed without decoding every graph a second time (most of the export's
     * cost). Only used when the kill sets are computed in the builder and thread escape is off. If the
     * analysis rebuilds a graph, the newer one replaces the older; a method with no recording is
     * decoded again as usual. Call before the analysis starts.
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
                // Don't let a scan failure break the analysis: the export decodes this graph again and reports the problem there.
                graphs.remove(method);
            }
            RECORDING_NANOS.addAndGet(System.nanoTime() - start);
        });
    }

    /** Stops recording and drops what was recorded. */
    public static void stopRecording(PointsToAnalysis bb) {
        bb.setGraphListener(null);
        recorded = null;
    }

    /**
     * Nodes that kill any location (so they make a method opaque) but never store a reference that
     * thread escape needs to follow: class initialization, Java/native transitions, writes of the
     * current-thread register, identity hash codes written into an object header, barriers, string
     * searches. Raw and unsafe reference stores, atomics included, are type flows of the analysis and
     * are handled as stores; a raw write to an address is not, and is treated like a call that may
     * keep its arguments.
     */
    private static final Set<String> STORES_NO_REFERENCE = Set.of("EnsureClassInitializedNode", "CEntryPointEnterNode", "CEntryPointLeaveNode", "CEntryPointUtilityNode",
                    "CFunctionPrologueNode", "CFunctionEpilogueNode", "SubstrateIdentityHashCodeNode", "WriteCurrentVMThreadNode", "WriteHeapBaseNode", "WriteCodeBaseNode",
                    "CompareAndSetVMThreadLocalNode", "VaListInitializationNode", "VaListNextArgNode", "ExceptionPathNode", "ValidateNewInstanceClassNode",
                    "SubstrateReflectionGetCallerClassNode", "FinalFieldBarrierNode", "SnippetSubstitutionNode", "ForeignCallNode", "RawStoreNode");

    /**
     * How completely the facts describe a method: not at all, partially (an unknown effect or call
     * that may store a reference), or fully.
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
     * The thread-escape assumptions named by {@code -Dsideeffects.assumptions} (comma-separated), or
     * none. See {@link ThreadEscape} for what each one means.
     */
    public static Set<String> defaultAssumptions() {
        String names = System.getProperty("sideeffects.assumptions", "");
        return names.isEmpty() ? Set.of() : Set.of(names.split(","));
    }

    /** Package prefixes that are not part of the program by default: the JDK, Native Image and Graal. */
    private static final String[] PLATFORM = {
                    "java.", "javax.", "jdk.", "sun.", "com.sun.",
                    "com.oracle.", "org.graalvm.",
                    "org.ietf.", "org.jcp.", "org.w3c.", "org.xml.",
    };

    /**
     * Whether a class belongs to the program. {@code prefixes} is a comma-separated list of class-name
     * prefixes; empty means every class outside the platform packages, and {@code *} means every
     * class.
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
     * Runs {@link #export(PointsToAnalysis, AnalysisUniverse, String, String, PrintStream, boolean, String, boolean, Set)}
     * with thread escape on and the assumptions from {@code -Dsideeffects.assumptions}.
     */
    public static void export(PointsToAnalysis bb, AnalysisUniverse universe, String jsonPath, String irPath, PrintStream report, boolean compiled, String programPrefix) {
        export(bb, universe, jsonPath, irPath, report, compiled, programPrefix, true, defaultAssumptions());
    }

    /**
     * Collects the facts of every reachable method and writes them (and, if requested, the program's
     * graphs) as JSON. Works on a finished analysis, either the standalone analyzer's or Native
     * Image's own. An empty path skips that file; {@code report} receives a human-readable summary,
     * or null for none.
     * <p>
     * {@code compiled}: the graphs will be compiled into an image, so a call the analysis found no
     * target for can never execute. {@code programPrefix}: which classes are the program (see
     * {@link #isProgramClass(String, String)}).
     * <p>
     * With {@code threadEscape}, the export also computes which objects other threads can reach and
     * records the objects of every lock and volatile access. Without it, the facts only say that a
     * method acquires or releases, and every acquire and release must be treated as synchronizing
     * with another thread. {@code assumptions} are extra assumptions for thread escape, described in
     * {@link ThreadEscape}; with none, the result follows from the analysis alone.
     */
    public static void export(PointsToAnalysis bb, AnalysisUniverse universe, String jsonPath, String irPath, PrintStream report, boolean compiled, String programPrefix,
                    boolean threadEscape, Set<String> assumptions) {
        export(bb, universe, jsonPath, irPath, report, compiled, programPrefix, threadEscape, assumptions, false);
    }

    /**
     * Like {@link #export(PointsToAnalysis, AnalysisUniverse, String, String, PrintStream, boolean, String, boolean, Set)},
     * and with {@code killSets} also computes the kill sets ({@link KillSetComputation}) and returns
     * them as {@code kills.txt} lines; returns null otherwise. With both paths empty nothing is
     * written. If graphs were recorded during the analysis (see {@link #recordDuringAnalysis}) and
     * thread escape is off, the kill sets come from the recorded graphs, and graphs are decoded again
     * only for what is written. A method whose graph fails to decode again is written from its
     * recorded graph, so the JSON and the builder's kill sets agree.
     */
    public static List<String> export(PointsToAnalysis bb, AnalysisUniverse universe, String jsonPath, String irPath, PrintStream report, boolean compiled, String programPrefix,
                    boolean threadEscape, Set<String> assumptions, boolean killSets) {
        STEP_NANOS.clear();
        SITE_LABEL_COLLISIONS.set(0);
        NOT_DECODED_AGAIN.set(0);
        long start = System.nanoTime();
        PrintStream out = report != null ? report : new PrintStream(OutputStream.nullOutputStream());
        // Name hidden classes first: names are keys, and keys decide the output order.
        GraphExport.nameHiddenClasses(universe.getTypes(), out);
        // Thread escape needs each node's objects, which a recorded graph doesn't keep.
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
            // Only build the report when someone reads it: it costs PetClinic's build two seconds.
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
        // For evaluation only: the shared objects under each set of assumptions, from one analysis.
        Map<String, TreeSet<String>> byAssumptions = threadEscape && System.getProperty("sideeffects.assumptionLayers") != null
                        ? sharedByAssumptions(bb, universe, found, compiled)
                        : new TreeMap<>();
        // Written method by method: with allocation-site sensitivity the facts and the shared objects can
        // each exceed the maximum String length (2^31 characters).
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
            // Written graph by graph: a framework's graphs can exceed the maximum String length.
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
     * For evaluation: the objects another thread may reach with no assumptions, then with each
     * assumption added in turn, and with the two that lock elision uses.
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

    /** The program's reachable methods with type flows, sorted by name and descriptor (the order graphs are written in). */
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

    /** The program's fields, each with whether the analysis saw it read and written. */
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

    /** Prints a human-readable summary of the program's methods: fields read and written, calls, and unknown effects. */
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

    /** Where diagnostics go (standard error); scripts read them from the build log. */
    static PrintStream diagnostics() {
        // Checkstyle: allow System.err (diagnostics that scripts read from the build's log)
        return System.err;
        // Checkstyle: disallow System.err
    }

    /** Adds the time since {@code start} to the named step and returns the current time. */
    static long step(String name, long start) {
        long now = System.nanoTime();
        STEP_NANOS.merge(name, now - start, Long::sum);
        return now;
    }

    /**
     * Collects the facts of every reachable method with type flows, in parallel. Each method's facts
     * are independent and merged into sorted maps, so the result does not depend on thread order.
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

    /** The facts the kill sets need for one method, replayed from the graph recorded during the analysis. */
    private static Facts recalled(PointsToAnalysisMethod ptm, Recorded graph, boolean compiled) {
        Facts f = new Facts();
        String name = GraphExport.methodKey(ptm);
        f.analysed.add(name);
        graph.replay(new Named(f, name, GraphExport.flows(ptm), compiled));
        flowFacts(ptm, name, f);
        return f;
    }

    /**
     * Collects one method's facts. If its graph cannot be decoded again after the analysis but was
     * recorded ({@code recordedGraphs}, null when not recording), the recorded graph is used instead.
     */
    private static Facts collect(PointsToAnalysis bb, PointsToAnalysisMethod ptm, boolean compiled, boolean threadEscape, String programPrefix, Map<AnalysisMethod, Recorded> recordedGraphs) {
        return new Collector(bb, ptm, compiled, threadEscape, programPrefix).collect(recordedGraphs);
    }

    /** Collects one method's facts: first from its graph, node by node, then from its type flows. */
    private static final class Collector {
        private final PointsToAnalysis bb;
        private final PointsToAnalysisMethod ptm;
        private final boolean compiled;
        private final boolean threadEscape;
        private final String name;
        private final Facts f = new Facts();

        /**
         * The type flows of the method's invokes, by call site. An invoke inlined before the analysis
         * shares the flow of its outermost call site with other invokes, so they are told apart by
         * target.
         */
        private Map<String, List<InvokeTypeFlow>> flows;
        /**
         * Resolves what an access's receiver may point to; only for the program's own methods. Elsewhere
         * an access is assumed to touch any object with that field or of that array kind.
         */
        private GraphExport.PointsTo pointsTo;
        /** The same, for locks and thread escape in any method; created lazily by {@link #synchronizedOn}. */
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
                // Use the graph the analysis built the flows from, replayed as in recalled(), so the JSON has the
                // same facts as the builder's kill sets.
                NOT_DECODED_AGAIN.incrementAndGet();
                f.analysed.add(name);
                graph.replay(new Named(f, name, GraphExport.flows(ptm), compiled));
            } else if (failure != null) {
                // Decoding fails when a plugin only works before Native Image seals its registries. Without a
                // graph the method may touch anything.
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

        /** Resolves the objects of locks, unsafe stores and opaque calls in methods outside the program; created on first use. */
        private GraphExport.PointsTo synchronizedOn() {
            if (synchronizedOn == null) {
                synchronizedOn = new GraphExport.PointsTo(bb, ptm);
            }
            return synchronizedOn;
        }

        /** Records what scan() doesn't: the objects of accesses and locks. Must test the same node kinds in the same order as scan(). */
        private void objects(Node n) {
            ValueNode[] unsafeStore = threadEscape ? unsafeStore(n) : null;
            if (unsafeStore != null) {
                // When the analysis is conservative about unsafe accesses, it doesn't model these stores at all.
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
                // scan() handles allocations.
            } else if (n instanceof Invoke invoke) {
                invoke(invoke, at(n));
            } else if (n instanceof FinalFieldBarrierNode && ptm.isConstructor()) {
                // As in scan().
            } else if (threadEscape && n instanceof AccessMonitorNode monitor && (MemoryKill.isMemoryKill(n) || n instanceof MemoryAccess) && !isBookkeeping(n)) {
                putSite(f.locks.computeIfAbsent(name, k -> new TreeMap<>()), GraphExport.simpleClassName(n) + at(n), synchronizedOn().objects(monitor.object()));
            }
        }

        /** Records calls that query or wait on a monitor, and calls into code the analysis can't see. */
        private void invoke(Invoke invoke, String at) {
            if (threadEscape && invoke.callTarget() != null && invoke.getTargetMethod() != null && isMonitorQuery(invoke.getTargetMethod()) && !invoke.callTarget().arguments().isEmpty()) {
                putSite(f.waits.computeIfAbsent(name, k -> new TreeMap<>()), invoke.getTargetMethod().getName() + at, synchronizedOn().objects(invoke.callTarget().arguments().get(0)));
            }
            if (threadEscape && flows.get(GraphExport.flowKey(invoke)) == null && invoke.callTarget() != null) {
                // A call into unseen code, e.g. through a function pointer: it may keep any object passed to it.
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
     * Adds what a method's type flows show beyond its graph: the fields loaded and stored, and the
     * resolved call targets (every target the analysis considers possible for a virtual call).
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
     * Reports what one node does to memory: field and array reads and writes, allocation, calls,
     * synchronization, and the locations any other memory node kills or reads (as Graal declares
     * them). The node is not named here; {@code found} names it, now or after the analysis.
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
            // Graal can't tell the element kind, so it says the copy kills anything. But System.arraycopy
            // only writes array elements, never a field: record a read and a write of every kind.
            for (JavaKind kind : List.of(JavaKind.Byte, JavaKind.Char, JavaKind.Short, JavaKind.Int, JavaKind.Long, JavaKind.Float, JavaKind.Double, JavaKind.Object)) {
                found.elements(kind, true);
                found.elements(kind, false);
            }
        } else if (n instanceof AbstractNewObjectNode || n instanceof CommitAllocationNode) {
            found.allocates();
        } else if (n instanceof ObjectClone) {
            // Graal says a clone kills anything. It writes only the new object, which no caller can have
            // read, and reads all of the original.
            found.allocates();
            found.unknownRead(GraphExport.simpleClassName(n), bci(n));
        } else if (n instanceof Invoke invoke) {
            found.call(GraphExport.flowBci(invoke), invoke.getTargetMethod(), bci(n));
        } else if (n instanceof FinalFieldBarrierNode && constructor) {
            // Ordering is carried by the reference: the token-form translation has a constructor return
            // its receiver, and later uses take that value.
        } else if ((MemoryKill.isMemoryKill(n) || n instanceof MemoryAccess) && !isBookkeeping(n)) {
            effects(n, found);
        }
    }

    /** The node's innermost bytecode index, or -1. */
    private static int bci(Node n) {
        return n instanceof ValueNode value ? GraphExport.bci(value) : -1;
    }

    /** The node's position as used in fact labels: " at bci N". */
    private static String at(Node n) {
        return at(bci(n));
    }

    private static String at(int bci) {
        return " at bci " + bci;
    }

    /** Receives what {@link #scan} finds in a node, before anything is named. */
    private interface Scanned {
        /** A field read or write; {@code ordered} for a volatile access. */
        void field(ResolvedJavaField field, boolean read, boolean ordered, int bci);

        /** A read or write of array elements of one kind. */
        void elements(JavaKind kind, boolean read);

        void allocates();

        /** A call, by its outermost call site in the flows ({@link GraphExport#flowBci}) and its target. */
        void call(int flowBci, ResolvedJavaMethod target, int bci);

        /** A node that synchronizes, by its class's simple name. */
        void synchronizes(String node, int bci, boolean acquires, boolean releases);

        /** A node that may kill any location. */
        void unknown(String node, int bci);

        void kills(LocationIdentity location);

        void reads(LocationIdentity location);

        /** A node that may read any location. */
        void unknownRead(String node, int bci);
    }

    /** Records what {@link #scan} finds into one method's facts, checking each call against the method's final type flows. */
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
                // A volatile read is an acquire, a volatile write a release.
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
            // No flow, a disabled flow, or no callees: the analysis found no target.
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
     * Keeps what {@link #scan} found in a graph during the analysis, by reference, to be replayed
     * later when names are stable and the flows are final. Keeps only what the kill sets need, so no
     * plain reads.
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

        /** Replays the recorded findings into {@code to}, in the order scan found them. */
        void replay(Scanned to) {
            if (allocates) {
                to.allocates();
            }
            found.forEach(event -> event.accept(to));
        }
    }

    /** Sites whose label collided with another site in the same method, so their objects were merged. */
    private static final AtomicInteger SITE_LABEL_COLLISIONS = new AtomicInteger();

    /** Methods written from their recorded graph because their graph failed to decode again. */
    private static final AtomicInteger NOT_DECODED_AGAIN = new AtomicInteger();

    /**
     * Records the objects a lock, volatile access or wait may be on, under the site's label. The label
     * uses only the innermost bytecode index, so two nodes of one graph can share it (for example a
     * method's own lock and one inlined into it, both at bci 0). Both are kept, and the objects are
     * unknown if either's are, so a lock on shared objects is never judged by a thread-local one with
     * the same label.
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

    /** Whether the call waits on, notifies, or asks whether the thread holds an object's monitor. */
    private static boolean isMonitorQuery(ResolvedJavaMethod method) {
        String owner = method.getDeclaringClass().toJavaName(true);
        String name = method.getName();
        return owner.equals("java.lang.Object") && (name.equals("wait") || name.equals("wait0") || name.equals("notify") || name.equals("notifyAll")) ||
                        owner.equals("java.lang.Thread") && name.equals("holdsLock");
    }

    /** For a node that stores a reference at an offset (unsafe put, CAS, exchange): the object and the value; null otherwise. */
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

    /** The facts of one method, or of all methods once merged, keyed by method name. */
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
        // Per method: the objects each acquire and release synchronizes on, where the analysis can name
        // them (a lock's object, a volatile field's receivers).
        final TreeMap<String, TreeMap<String, Object>> locks = new TreeMap<>();
        // Per method: the objects its wait, notify, notifyAll and holdsLock calls are on, where the
        // analysis can name them. An object that is waited on must keep its monitor.
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

        /** Writes the facts as the JSON "methods" and "fields", one entry at a time. */
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
     * Nodes that kill or read memory only for Graal's bookkeeping: the start and handler-entry states,
     * creating an exception on a throwing path, and an array length (which never changes).
     */
    private static boolean isBookkeeping(Node n) {
        return n instanceof StartNode || n instanceof ExceptionObjectNode || n instanceof BytecodeExceptionNode || n instanceof ArrayLengthNode;
    }

    /**
     * Handles any other memory node by what Graal declares it kills and reads. Synchronization (an
     * ordered access, a lock, a fence, an atomic update) becomes an acquire, a release or both. Any
     * other kill of any location is an unknown effect. A read of any location is recorded too: it
     * matters to the token form, not to what a call may write.
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
     * What a synchronizing node does under the Java memory model. After an acquire, this thread may
     * see what other threads wrote before their release; after a release, other threads may see what
     * this thread wrote before it.
     */
    private record Synchronization(boolean acquires, boolean releases) {
        static final Synchronization ACQUIRE = new Synchronization(true, false);
        static final Synchronization RELEASE = new Synchronization(false, true);
        static final Synchronization BOTH = new Synchronization(true, true);
    }

    /**
     * Whether and how a node synchronizes; null if it doesn't. A lock enter acquires and a lock exit
     * releases. An ordered load acquires and an ordered store releases. An opaque access does neither
     * (counting it is merely conservative). Atomic updates, fences and other ordering nodes do both.
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
     * A method's name in the facts and in kills.txt: class, name and descriptor. Hidden classes
     * are named by content instead of address, as of the last export.
     */
    public static String methodKey(ResolvedJavaMethod method) {
        return GraphExport.methodKey(method);
    }

    /** A field's name in the facts; hidden classes as in {@link #methodKey}. */
    public static String fieldName(ResolvedJavaField field) {
        return GraphExport.fieldName(field);
    }

    /** A node's position as the facts and decisions name it: {@code method:bci}, then each caller outward. */
    public static String position(BytecodePosition position) {
        return GraphExport.PointsTo.site(position);
    }

    /**
     * A location's name in the facts: a field, an array kind, or {@code vm:} plus the name of a VM
     * location (e.g. {@code vm:TLAB.top}). Null for an immutable location.
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
     * Records a field or array access with its position and the objects its receiver may point to
     * (null if unknown), e.g. {"kind": "read", "field": "Examples$Counter.value", "receivers":
     * ["Examples$Counter@Examples.main([Ljava/lang/String;)V:9"], "at": "Examples.length(LExamples$Link;)I:5"}.
     */
    private static void addAccess(TreeMap<String, TreeSet<String>> accesses, String method, String kind, String field, List<String> receivers, Node node) {
        Map<String, Object> access = new LinkedHashMap<>();
        access.put("kind", kind);
        access.put("field", field);
        access.put("receivers", receivers);
        access.put("at", GraphExport.PointsTo.site(node instanceof ValueNode value ? value.getNodeSourcePosition() : null));
        add(accesses, method, GraphExport.toJson(access, 2));
    }

    /** Text written to a file in pieces, because a large export doesn't fit in one String. */
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
