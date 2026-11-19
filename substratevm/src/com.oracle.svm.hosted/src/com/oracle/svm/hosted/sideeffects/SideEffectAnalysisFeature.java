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
package com.oracle.svm.hosted.sideeffects;

import java.io.IOException;
import java.io.PrintStream;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeSet;

import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.export.PointsToExport;
import com.oracle.svm.core.feature.InternalFeature;
import com.oracle.svm.core.graal.phases.RemoveUnwindPhase;
import com.oracle.svm.core.util.UserError;
import com.oracle.svm.hosted.FeatureImpl;
import com.oracle.svm.shared.feature.AutomaticallyRegisteredFeature;
import com.oracle.svm.shared.option.HostedOptionKey;

import jdk.graal.compiler.options.Option;
import jdk.graal.compiler.options.OptionStability;
import jdk.graal.compiler.phases.BasePhase;
import jdk.graal.compiler.phases.Phase;
import jdk.graal.compiler.phases.tiers.HighTierContext;
import jdk.graal.compiler.phases.tiers.Suites;
import jdk.graal.compiler.phases.util.Providers;

/**
 * Narrows what calls may write, using the closed-world points-to analysis, so that Graal's own
 * memory optimizations (read elimination, floating reads, loop-invariant motion) work across calls
 * they can't see into. Enabled with {@code -H:+SideEffectAnalysis}; options are in {@link Options}.
 * <p>
 * One build goes like this:
 * <ol>
 * <li>After the points-to analysis, {@link PointsToExport} collects each reachable method's facts:
 * what it reads and writes, allocates, calls and synchronizes on.</li>
 * <li>From the facts, each method gets a kill set: what a call to it may write, including through
 * its callees, or {@code any} if that can't be bounded. This is computed either in the builder
 * ({@code -H:SideEffectAnalysisKillSets=build}, {@code KillSetComputation}) or by the Python tool
 * {@code effects.kills} on a JSON export. See {@link KillSets}.</li>
 * <li>Right after Native Image's inliners, {@link ApplySideEffectAnalysisPhase} gives every call
 * in the program's methods (inlined ones included) the union of its possible callees' kill sets.
 * Graal's existing phases then do the optimizing.</li>
 * <li>Optionally, field accesses get partitioned locations ({@link FieldPartitions}), locks on
 * thread-local objects are removed ({@link LockElision}), and overwritten stores are removed
 * ({@link EliminateOverwrittenStoresPhase}).</li>
 * <li>At the end of the low tier, {@link CompiledCodeCounts} counts the loads, stores and calls
 * left in the program's methods; {@code timings.txt} records what each step cost
 * ({@link StepTimes}).</li>
 * </ol>
 * With {@code -H:Dump=:1}, the graph is dumped right after the calls are narrowed ("After applying
 * the side-effect analysis").
 * <p>
 * Every narrowed call also kills the VM state that a safepoint in a callee may change, as Native
 * Image's own safepoints do: notably the allocation buffer, which a GC resets. Allocations are
 * lowered after the memory graph is built, so without this kill an allocation after the call could
 * use a buffer pointer read before it. No call kills init memory: a callee initializes, publishes
 * and fences what it allocates before returning ({@code PublishWritesNode}), and
 * {@code InitMemoryVerificationPhase} would treat a kill of init memory as an initializing write
 * that needs a barrier.
 */
@AutomaticallyRegisteredFeature
public final class SideEffectAnalysisFeature implements InternalFeature {

    public static final class Options {
        @Option(help = "Narrow the memory each call may write, using the points-to analysis' view of its callees, so Graal's memory optimizations can work across calls. Optionally partition field locations by object.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysis = new HostedOptionKey<>(false);

        @Option(help = "Path to the explicit-effects checkout, whose Python tool computes kill sets and lock decisions when they are not computed in the builder. Run with uv.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisTool = new HostedOptionKey<>(".");

        @Option(help = "The uv executable used to run the Python tool, in case the builder's environment doesn't find it.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisUv = new HostedOptionKey<>("uv");

        @Option(help = "Output directory: the export, kill sets, per-method counts of what Graal leaves, and the time each step took.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisOutput = new HostedOptionKey<>("side-effect-analysis");

        @Option(help = "Comma-separated class-name prefixes of the program: its methods get narrowed calls and are counted. " +
                        "Empty: every class outside the JDK, Native Image and Graal. *: every class in the image.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisProgram = new HostedOptionKey<>("");

        @Option(help = "Narrow the calls. Off: nothing is narrowed and the feature only counts what Graal leaves (the baseline).", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisNarrowCalls = new HostedOptionKey<>(true);

        @Option(help = "How memory is partitioned. field: Graal's usual per-field locations. object-field: also split a field by groups of objects that no access mixes; " +
                        "needs -H:AnalysisContextSensitivity=allocsens and -H:+TrackNodeSourcePosition.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisPartition = new HostedOptionKey<>("field");

        @Option(help = "Also run OverwrittenStoreEliminationPhase on the program's methods, right after the calls are narrowed. " +
                        "With partitions it can remove stores that are overwritten before they can be read.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisEliminateOverwrittenStores = new HostedOptionKey<>(false);

        @Option(help = "Also export the program's graphs, for the tool's translation to the token form (graal2ct).", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisExportGraphs = new HostedOptionKey<>(false);

        @Option(help = "Narrow calls only in methods with these comma-separated name prefixes (as the export names methods). For debugging.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisOnlyMethods = new HostedOptionKey<>("");

        @Option(help = "Don't narrow calls in methods with these comma-separated name prefixes (as the export names methods). For debugging.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisSkipMethods = new HostedOptionKey<>("");

        @Option(help = "Every narrowed call also kills the VM state a safepoint may change (allocation buffer, safepoint counter). Off is unsafe; for testing only.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisKillVMState = new HostedOptionKey<>(true);

        @Option(help = "Narrowed calls also kill the JDK and VM fields their callees write. Off is unsafe; for testing only: images must break.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisKillPlatformFields = new HostedOptionKey<>(true);

        @Option(help = "Test only, deliberately unsound: claim that this method (as the export names it) writes nothing. The program's output must then go wrong.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisClaimWritesNothing = new HostedOptionKey<>("");

        @Option(help = "Test only, deliberately unsound: in this method, claim that different references never point to the same object. The program's output must then go wrong.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisClaimNoAliasing = new HostedOptionKey<>("");

        @Option(help = "Compute which objects other threads can reach, and record the objects of locks and volatile accesses. " +
                        "Off: every acquire and release counts as synchronizing with another thread, and no lock or volatile access can be removed or made plain. " +
                        "Required by -H:+SideEffectAnalysisElideLocks, the assumptions and the lock claims.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisThreadEscape = new HostedOptionKey<>(true);

        @Option(help = "Comma-separated assumptions thread escape may make beyond what the points-to analysis shows: " +
                        "thread-confined (a thread's park blocker and thread locals are read only by that thread), " +
                        "vm-fields (the VM's own fields are read only by the VM), " +
                        "vm-code (VM code stores references only where VM code reads them), " +
                        "handler-references (the reference handler thread never reads a referent), " +
                        "entry-points (the VM's calls into the analysis roots pass only shared objects and publish nothing the roots return). " +
                        "Empty: none. entry-points needs -H:+TrackInputFlows to have an effect.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisAssumptions = new HostedOptionKey<>("");

        @Option(help = "Remove locks on objects only one thread can reach and that nothing waits on or notifies, as the tool decides (effects.elide), and make volatile accesses on such objects plain. " +
                        "Needs -H:+TrackNodeSourcePosition and thread-escape assumptions to find any. Images that can deoptimize keep their locks.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisElideLocks = new HostedOptionKey<>(false);

        @Option(help = "Test only, deliberately unsound: claim that every lock and volatile access in this method (as the export names it) is on a thread-local object, " +
                        "so they are removed or made plain. A program that shares them must then go wrong.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisClaimLocksLocal = new HostedOptionKey<>("");

        @Option(help = "Test only, deliberately unsound: remove listed locks even in an image that can deoptimize. " +
                        "Code deoptimized inside a removed lock must then leave the thread holding the lock.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisClaimNoDeoptimization = new HostedOptionKey<>(false);

        @Option(help = "Measurement only, never sound: treat these kinds of effect as writing nothing when computing kill sets " +
                        "(identity-hash, class-initialization, synchronization, unresolved-calls, calls-without-facts, other-effects; all: every one). " +
                        "Gives an upper bound on what more precise kill sets could gain. The image may be wrong; always compare its output with the JVM's.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisIgnoreEffects = new HostedOptionKey<>("");

        @Option(help = "Name of this configuration in the counts. Empty: derived from the other options (graal, fields, objects or graal-dse).", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisLabel = new HostedOptionKey<>("");

        @Option(help = "Where the kill sets are computed. tool: the Python tool (effects.kills) on the JSON export. " +
                        "build: in the image builder (KillSetComputation), with no export unless lock elision or the graphs need one; without thread escape it reuses the graphs the analysis built, so no graph is decoded again. " +
                        "both: both, and the build fails if they differ. build and both support only per-field partitions and no ignored effects.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisKillSets = new HostedOptionKey<>("tool");
    }

    private final Path out = Path.of(Options.SideEffectAnalysisOutput.getValue());
    private final String program = Options.SideEffectAnalysisProgram.getValue();
    private final boolean narrow = Options.SideEffectAnalysisNarrowCalls.getValue();
    private final String partition = Options.SideEffectAnalysisPartition.getValue();
    private final boolean overwrittenStores = Options.SideEffectAnalysisEliminateOverwrittenStores.getValue();
    /**
     * Whether the export includes the program's graphs. Only the token-form translation (graal2ct)
     * needs them; kill sets and partitions need only the facts, so writing graphs is wasted otherwise.
     */
    private final boolean graphs = Options.SideEffectAnalysisExportGraphs.getValue();
    private final boolean elideLocks = Options.SideEffectAnalysisElideLocks.getValue();
    private final boolean threadEscape = Options.SideEffectAnalysisThreadEscape.getValue();
    private final String ignoredEffects = Options.SideEffectAnalysisIgnoreEffects.getValue();
    private final String killSetsBy = Options.SideEffectAnalysisKillSets.getValue();
    private final List<String> only = prefixes(Options.SideEffectAnalysisOnlyMethods.getValue());
    private final List<String> skip = prefixes(Options.SideEffectAnalysisSkipMethods.getValue());
    private final String label = !Options.SideEffectAnalysisLabel.getValue().isEmpty() ? Options.SideEffectAnalysisLabel.getValue()
                    : !narrow ? "graal" : overwrittenStores ? "graal-dse" : partition.equals("field") ? "fields" : "objects";

    private final StepTimes times = new StepTimes();
    private final KillSets killSets = new KillSets(program, Options.SideEffectAnalysisKillVMState.getValue(), Options.SideEffectAnalysisKillPlatformFields.getValue());
    private final FieldPartitions partitions = new FieldPartitions(Options.SideEffectAnalysisClaimNoAliasing.getValue());
    private final LockElision lockElision = new LockElision(Options.SideEffectAnalysisClaimLocksLocal.getValue(), Options.SideEffectAnalysisClaimNoDeoptimization.getValue());
    private final CompiledCodeCounts counts = new CompiledCodeCounts(program);
    /** Size of export.json for timings.txt; 0 if none was written. */
    private long exportBytes;
    /** Number of methods whose builder and tool kill sets were compared and found equal; -1 if not compared. */
    private int killSetsCompared = -1;

    @Override
    public boolean isInConfiguration(IsInConfigurationAccess access) {
        return Options.SideEffectAnalysis.getValue();
    }

    @Override
    public void beforeAnalysis(BeforeAnalysisAccess access) {
        // Thread escape needs each node's objects, which only a graph decoded after the analysis gives.
        if (narrow && !killSetsBy.equals("tool") && !threadEscape && ((FeatureImpl.BeforeAnalysisAccessImpl) access).getBigBang() instanceof PointsToAnalysis bb) {
            PointsToExport.recordDuringAnalysis(bb);
        }
    }

    @Override
    public void afterAnalysis(AfterAnalysisAccess access) {
        if (!narrow && !elideLocks) {
            return;
        }
        Path export = out.resolve("export.json");
        try {
            Files.createDirectories(out);
            List<String> worked = export((FeatureImpl.AfterAnalysisAccessImpl) access, export);
            if (elideLocks) {
                readLockDecisions(export);
            }
            if (!narrow) {
                return;
            }
            readKillSets(export, worked);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        } catch (InterruptedException e) {
            throw new IllegalStateException(e);
        }
        String lie = Options.SideEffectAnalysisClaimWritesNothing.getValue();
        if (!lie.isEmpty()) {
            killSets.claimWritesNothing(lie);
        }
    }

    /**
     * Collects the facts and records what each step cost. When the builder computes the kill sets,
     * returns them as kills.txt lines and writes the JSON export only if something still reads it (the
     * tool, for {@code both}; lock elision; the graphs). Returns null when the tool computes them.
     */
    private List<String> export(FeatureImpl.AfterAnalysisAccessImpl access, Path export) throws IOException {
        long start = System.nanoTime();
        String assumptions = Options.SideEffectAnalysisAssumptions.getValue();
        boolean inBuild = narrow && !killSetsBy.equals("tool");
        checkOptions(assumptions, inBuild);
        boolean written = !(narrow && killSetsBy.equals("build")) || elideLocks || graphs;
        if (!written) {
            // Not written by this build: delete it so nothing reads a stale export from an earlier build.
            Files.deleteIfExists(export);
        }
        Set<String> assumed = assumptions.isEmpty() ? PointsToExport.defaultAssumptions() : Set.of(assumptions.split(","));
        // The export goes to one of two paths depending on whether it includes graphs; "" writes nothing.
        String factsOnly = written && !graphs ? export.toString() : "";
        String withGraphs = written && graphs ? export.toString() : "";
        PrintStream report = null; // no human-readable summary
        boolean compiled = true; // the image is compiled next, so a call without targets can never execute
        List<String> worked = PointsToExport.export((PointsToAnalysis) access.getBigBang(), access.getUniverse(), factsOnly, withGraphs, report, compiled, program, threadEscape, assumed, inBuild);
        PointsToExport.stopRecording((PointsToAnalysis) access.getBigBang());
        times.time("export", start);
        PointsToExport.STEP_NANOS.forEach((step, stepNanos) -> times.add("export: " + step, stepNanos));
        exportBytes = written ? Files.size(export) : 0;
        return worked;
    }

    /** Fails the build on options that can't be combined. */
    private void checkOptions(String assumptions, boolean inBuild) {
        if (!threadEscape && (elideLocks || !assumptions.isEmpty() || !Options.SideEffectAnalysisClaimLocksLocal.getValue().isEmpty())) {
            throw UserError.abort(
                            "-H:-SideEffectAnalysisThreadEscape leaves out what -H:+SideEffectAnalysisElideLocks, -H:SideEffectAnalysisAssumptions and -H:SideEffectAnalysisClaimLocksLocal need");
        }
        if (!List.of("tool", "build", "both").contains(killSetsBy)) {
            throw UserError.abort("-H:SideEffectAnalysisKillSets is tool, build or both, not %s", killSetsBy);
        }
        if (inBuild && (!partition.equals("field") || !ignoredEffects.isEmpty())) {
            throw UserError.abort("-H:SideEffectAnalysisKillSets=%s partitions by field and leaves no effect out: -H:SideEffectAnalysisPartition and -H:SideEffectAnalysisIgnoreEffects need the tool",
                            killSetsBy);
        }
    }

    /** Runs effects.elide on the export and reads which locks and volatile accesses can go. */
    private void readLockDecisions(Path export) throws IOException, InterruptedException {
        Path locks = out.resolve("locks.txt");
        runTool("effects.elide", export, export.toString(), "-o", locks.toString());
        lockElision.read(locks);
    }

    /**
     * Reads each method's kill set: computed by the builder ({@code worked}) or by effects.kills from
     * the export, which also gives each access its partition for object-field partitions. With
     * {@code both}, fails the build if the two disagree.
     */
    private void readKillSets(Path export, List<String> worked) throws IOException, InterruptedException {
        Path kills = out.resolve("kills.txt");
        if (killSetsBy.equals("build")) {
            // Write the same kills.txt the tool would, for scripts that read it after the build.
            Files.write(kills, worked);
            killSets.read(worked);
            return;
        }
        Path accesses = out.resolve("accesses.txt");
        List<String> arguments = new ArrayList<>(List.of(export.toString(), "-o", kills.toString(), "--partition", partition));
        if (!partition.equals("field")) {
            arguments.addAll(List.of("--accesses", accesses.toString()));
        }
        if (!ignoredEffects.isEmpty()) {
            arguments.addAll(List.of("--ignore", ignoredEffects));
        }
        runTool("effects.kills", export, arguments.toArray(new String[0]));
        List<String> byTool = Files.readAllLines(kills);
        killSets.read(byTool);
        if (killSetsBy.equals("both")) {
            compare(byTool, worked);
        }
        if (!partition.equals("field")) {
            partitions.read(accesses);
        }
    }

    /** Fails the build if any builder kill set differs from the tool's; the builder's are left in kills-build.txt. */
    private void compare(List<String> byTool, List<String> worked) throws IOException {
        Map<String, String> tool = byMethod(byTool);
        Map<String, String> build = byMethod(worked);
        TreeSet<String> methods = new TreeSet<>(tool.keySet());
        methods.addAll(build.keySet());
        List<String> differ = new ArrayList<>();
        for (String method : methods) {
            if (!Objects.equals(tool.get(method), build.get(method))) {
                differ.add(method + ": tool " + tool.get(method) + ", build " + build.get(method));
            }
        }
        if (!differ.isEmpty()) {
            Files.write(out.resolve("kills-build.txt"), worked);
            throw UserError.abort("%d of %d methods have another kill set in the build than in the tool (kills-build.txt against kills.txt), the first: %s", differ.size(), methods.size(),
                            String.join("; ", differ.subList(0, Math.min(5, differ.size()))));
        }
        killSetsCompared = methods.size();
    }

    /** kills.txt lines by method: the part after the tab. */
    private static Map<String, String> byMethod(List<String> lines) {
        Map<String, String> byMethod = new HashMap<>();
        for (String line : lines) {
            int tab = line.indexOf('\t');
            byMethod.put(line.substring(0, tab), line.substring(tab + 1));
        }
        return byMethod;
    }

    /** Runs a module of the Python tool on the export ({@code python -m module arguments}) as a timed step. */
    private void runTool(String module, Path export, String... arguments) throws IOException, InterruptedException {
        List<String> command = new ArrayList<>(List.of(Options.SideEffectAnalysisUv.getValue(), "run", "--project", Options.SideEffectAnalysisTool.getValue(), "python", "-m", module));
        command.addAll(List.of(arguments));
        long start = System.nanoTime();
        runToEnd(new ProcessBuilder(command), module, export);
        times.time(module, start);
    }

    /**
     * Runs a tool process to completion, and kills it and its children if the image generator exits
     * first. The generator's watchdog aborts a step that takes ten minutes
     * (-H:DeadlockWatchdogInterval), and a tool left running would keep using the machine's memory.
     */
    private static void runToEnd(ProcessBuilder builder, String name, Path export) throws IOException, InterruptedException {
        Process tool = builder.inheritIO().start();
        Thread stop = new Thread(() -> stopTree(tool));
        Runtime.getRuntime().addShutdownHook(stop);
        try {
            if (tool.waitFor() != 0) {
                throw new IllegalStateException(name + " failed on " + export);
            }
        } finally {
            stopTree(tool);
            try {
                Runtime.getRuntime().removeShutdownHook(stop);
            } catch (IllegalStateException e) {
                // the generator is already exiting: the shutdown hook runs
            }
        }
    }

    /** Kills a process and every process it started. */
    private static void stopTree(Process tool) {
        tool.descendants().forEach(ProcessHandle::destroyForcibly);
        tool.destroyForcibly();
    }

    @Override
    public void beforeCompilation(BeforeCompilationAccess access) {
        killSets.useImage(((FeatureImpl.BeforeCompilationAccessImpl) access).getUniverse());
    }

    @Override
    public void registerGraalPhases(Providers providers, Suites suites, boolean hosted, boolean fallback) {
        if (hosted) {
            if (narrow || elideLocks) {
                /*
                 * Insert after Native Image's inliners (where RemoveUnwindPhase is), so that calls and stores
                 * inlining brings in are narrowed too. Before the inliners only canonicalization runs, which
                 * no kill set affects.
                 */
                List<Phase> phases = highTierPhases();
                ListIterator<BasePhase<? super HighTierContext>> afterInlining = suites.getHighTier().findPhase(RemoveUnwindPhase.class);
                if (afterInlining != null) {
                    phases.forEach(afterInlining::add);
                } else {
                    Collections.reverse(phases);
                    phases.forEach(suites.getHighTier()::prependPhase);
                }
            }
            if (!partition.equals("field")) {
                suites.getMidTier().prependPhase(new VerifyFieldPartitionsPhase(times));
            }
            suites.getLowTier().appendPhase(counts.newPhase(times));
        }
    }

    /** The phases inserted after the inliners, in order: narrowing calls, overwritten stores, lock elision. */
    private List<Phase> highTierPhases() {
        List<Phase> phases = new ArrayList<>();
        if (narrow) {
            phases.add(new ApplySideEffectAnalysisPhase(times, killSets, partitions, program, only, skip, counts));
            if (overwrittenStores) {
                phases.add(new EliminateOverwrittenStoresPhase(times, program, counts));
            }
        }
        if (elideLocks) {
            phases.add(lockElision.newPhase(times, counts));
        }
        return phases;
    }

    @Override
    public void afterCompilation(AfterCompilationAccess access) {
        try {
            Files.createDirectories(out);
            counts.write(out, label);
            Files.writeString(out.resolve("timings.txt"), timings());
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /** Contents of timings.txt: each step's cost, then notes on the export, the kill sets and the locks. */
    private StringBuilder timings() {
        StringBuilder timings = new StringBuilder("# step\tseconds\truns (the export and the tool once, a phase once per graph, summed over the compiler's threads)\n");
        times.appendTo(timings);
        timings.append(String.format("# export.json: %d bytes, %d methods with facts%n", exportBytes, killSets.methodsWithFacts()));
        if (killSetsCompared >= 0) {
            timings.append(String.format("# kill sets worked out in the build: the tool's for all %d methods%n", killSetsCompared));
        }
        if (!ignoredEffects.isEmpty()) {
            timings.append(String.format("# the kill of %s is left out of the kill sets: an upper bound, not sound%n", ignoredEffects));
        }
        if (elideLocks) {
            lockElision.appendTo(timings);
        }
        return timings;
    }

    /** The entries of a comma-separated option; none for an empty one. */
    private static List<String> prefixes(String commaSeparated) {
        return Arrays.stream(commaSeparated.split(",")).filter(prefix -> !prefix.isEmpty()).toList();
    }
}
