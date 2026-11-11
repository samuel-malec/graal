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
 * Applies a side-effect analysis to the image's compilation, in one native-image build. After the
 * points-to analysis, the feature exports its results ({@link PointsToExport}) and runs the
 * explicit-effects tool on them (effects.kills), which says what each method, with everything it
 * calls, may write ({@link KillSets}); with {@code -H:SideEffectAnalysisKillSets=build} the
 * builder works that out itself from the same facts, without the export. Right after Native Image
 * inlines, every call in the program's methods, the inlined ones included, kills only those
 * locations instead of all of memory, and Graal's own phases do the rest
 * ({@link ApplySideEffectAnalysisPhase}). The tool can
 * also give each access to a field the location of its partition of the objects
 * ({@link FieldPartitions}). A phase at the end of the low tier counts the field stores, field
 * loads and calls left in the program's methods ({@link CompiledCodeCounts}), and timings.txt
 * records what each step of the analysis cost in the build ({@link StepTimes}).
 * <p>
 * Enabled with {@code -H:+SideEffectAnalysis}; the other options are in {@link Options}. With
 * {@code -H:Dump=:1}, the graph is dumped right after the analysis is applied, titled "After
 * applying the side-effect analysis".
 * <p>
 * Every narrowed call also kills what a safepoint in its callees may change, as Native Image's
 * own safepoints do: the thread's allocation buffer, which a collection resets. Native Image
 * lowers an allocation after the memory graph is built, so its read of the buffer would otherwise
 * come from before the call. No call kills init memory: a callee initializes, publishes and fences
 * what it allocates before it returns ({@code PublishWritesNode}), and Graal takes a kill of init
 * for an initializing write that a barrier must follow ({@code InitMemoryVerificationPhase}).
 */
@AutomaticallyRegisteredFeature
public final class SideEffectAnalysisFeature implements InternalFeature {

    public static final class Options {
        @Option(help = "Apply a side-effect analysis (the explicit-effects tool) to the compilation: narrow what each call kills, and optionally partition field locations.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysis = new HostedOptionKey<>(false);

        @Option(help = "The explicit-effects checkout whose tool computes the side effects; it runs with uv.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisTool = new HostedOptionKey<>(".");

        @Option(help = "The uv executable that runs the side-effect tool, as the builder's environment may not find it.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisUv = new HostedOptionKey<>("uv");

        @Option(help = "Directory for the exported points-to results, the tool's answers, the counts of what Graal leaves and what each step of the analysis cost.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisOutput = new HostedOptionKey<>("side-effect-analysis");

        @Option(help = "Comma-separated class-name prefixes of the program whose calls are narrowed and whose accesses are counted, and that the export describes. " +
                        "Empty: every class outside the platform's packages; *: every class.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisProgram = new HostedOptionKey<>("");

        @Option(help = "Narrow what each call kills. Off, the feature only counts what Graal leaves, as a baseline.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisNarrowCalls = new HostedOptionKey<>(true);

        @Option(help = "How finely memory is partitioned: field keeps Graal's locations; object-field also splits each field by the sets of objects points-to analysis tells apart, " +
                        "which needs -H:AnalysisContextSensitivity=allocsens and -H:+TrackNodeSourcePosition.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisPartition = new HostedOptionKey<>("field");

        @Option(help = "Also run Graal's OverwrittenStoreEliminationPhase on the program's methods, right after the analysis is applied: " +
                        "with the partitions, it removes the stores that are overwritten before anything reads them.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisEliminateOverwrittenStores = new HostedOptionKey<>(false);

        @Option(help = "Also export the program's graphs, to translate them with the tool afterwards (graal2ct).", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisExportGraphs = new HostedOptionKey<>(false);

        @Option(help = "Comma-separated method prefixes, as the export names methods: narrow the calls of only these methods.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisOnlyMethods = new HostedOptionKey<>("");

        @Option(help = "Comma-separated method prefixes, as the export names methods: narrow the calls of all methods but these.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisSkipMethods = new HostedOptionKey<>("");

        @Option(help = "Have every narrowed call also kill the VM state a safepoint may change. Off is a control that must break images.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisKillVMState = new HostedOptionKey<>(true);

        @Option(help = "Have narrowed calls kill the platform's fields they write. Off is a control that must break images.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisKillPlatformFields = new HostedOptionKey<>(true);

        @Option(help = "Control: a method, as the export names it, claimed to write nothing, so that a wrong answer shows in the program's output.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisClaimWritesNothing = new HostedOptionKey<>("");

        @Option(help = "Control: a method in which different references are claimed never to meet, as an unsound points-to analysis would, so that a wrong partition shows in the output.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisClaimNoAliasing = new HostedOptionKey<>("");

        @Option(help = "Work out which objects other threads can reach, and record the locks and volatile accesses to judge them by. " +
                        "Off (-H:-SideEffectAnalysisThreadEscape) the facts say only that a method acquires or releases, with no list of shared objects, " +
                        "so every acquire and release counts as ordering this thread with another, and no lock or volatile access can be removed or made ordinary: " +
                        "the side-effect analysis then does nothing that depends on a model of concurrency. " +
                        "Not with -H:+SideEffectAnalysisElideLocks, the assumptions or the lock claims.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisThreadEscape = new HostedOptionKey<>(true);

        @Option(help = "Comma-separated assumptions thread escape makes on top of what the points-to analysis shows: " +
                        "thread-confined (the object a thread parks on and its thread locals are read only by it), " +
                        "vm-fields (the virtual machine's own state is read only by it), " +
                        "vm-code (the virtual machine's code stores references only where it reads them), " +
                        "handler-references (the reference handler thread never reads a referent), " +
                        "entry-points (the callers of the roots outside the analysed code pass only shared objects and keep nothing the roots return). " +
                        "Empty: none. The analysis must track the inputs of its flows (-H:+TrackInputFlows) for the last to matter.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisAssumptions = new HostedOptionKey<>("");

        @Option(help = "Remove the monitor enters and exits on objects that only one thread reaches and nothing waits or notifies on, as the tool decides (effects.elide). " +
                        "Needs -H:+TrackNodeSourcePosition, and thread escape assumptions to find any. An image that can deoptimize keeps its monitors.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisElideLocks = new HostedOptionKey<>(false);

        @Option(help = "Control: a method, as the export names it, whose monitors and volatile accesses are claimed to be on objects only one thread reaches, " +
                        "so that they are removed or made ordinary whatever the tool says; a program that shares them must then go wrong.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisClaimLocksLocal = new HostedOptionKey<>("");

        @Option(help = "Control: remove the monitors the tool lists in an image that can deoptimize as well, which the image otherwise keeps; " +
                        "code compiled while the program runs and deoptimized inside a locked region must then leave the thread holding the lock.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisClaimNoDeoptimization = new HostedOptionKey<>(false);

        @Option(help = "Control, never sound: comma-separated effects whose kill is left out of the kill sets " +
                        "(identity-hash, class-initialization, synchronization, unresolved-calls, calls-without-facts, other-effects; all: every one), " +
                        "to measure the most that precise kill sets could give Graal. The image may be wrong; its output must still be compared with the JVM's.", //
                        stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisIgnoreEffects = new HostedOptionKey<>("");

        @Option(help = "How the counts name this build. Empty: from the other options (graal, fields, objects or graal-dse).", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisLabel = new HostedOptionKey<>("");

        @Option(help = "Where the kill sets are worked out: tool runs the explicit-effects tool (effects.kills) on the export; " +
                        "build works them out in the image builder from the same facts, as the tool does, and writes no export unless lock elision or the graphs need it; " +
                        "both does both and stops the build if they differ. build and both partition by field and leave no effect out.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisKillSets = new HostedOptionKey<>("tool");
    }

    private final Path out = Path.of(Options.SideEffectAnalysisOutput.getValue());
    private final String program = Options.SideEffectAnalysisProgram.getValue();
    private final boolean narrow = Options.SideEffectAnalysisNarrowCalls.getValue();
    private final String partition = Options.SideEffectAnalysisPartition.getValue();
    private final boolean overwrittenStores = Options.SideEffectAnalysisEliminateOverwrittenStores.getValue();
    /**
     * Whether the export holds the program's graphs, which the translation (graal2ct) needs; the
     * kill sets and partitions need only the facts, so writing and reading the graphs is cost they
     * don't need.
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
    private long exportBytes;
    /** For how many methods the build's kill sets were found equal to the tool's; -1 if not compared. */
    private int killSetsCompared = -1;

    @Override
    public boolean isInConfiguration(IsInConfigurationAccess access) {
        return Options.SideEffectAnalysis.getValue();
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
     * Exports what the points-to analysis found, and adds what its steps cost to the timings. When
     * the build works out the kill sets, returns them as the tool writes them, and writes the export
     * only for what still reads it: the tool when the two are compared, lock elision, the graphs.
     * Null when the tool works them out.
     */
    private List<String> export(FeatureImpl.AfterAnalysisAccessImpl access, Path export) throws IOException {
        long start = System.nanoTime();
        String assumptions = Options.SideEffectAnalysisAssumptions.getValue();
        if (!threadEscape && (elideLocks || !assumptions.isEmpty() || !Options.SideEffectAnalysisClaimLocksLocal.getValue().isEmpty())) {
            throw UserError.abort("-H:-SideEffectAnalysisThreadEscape leaves out what -H:+SideEffectAnalysisElideLocks, -H:SideEffectAnalysisAssumptions and -H:SideEffectAnalysisClaimLocksLocal need");
        }
        if (!List.of("tool", "build", "both").contains(killSetsBy)) {
            throw UserError.abort("-H:SideEffectAnalysisKillSets is tool, build or both, not %s", killSetsBy);
        }
        boolean inBuild = narrow && !killSetsBy.equals("tool");
        if (inBuild && (!partition.equals("field") || !ignoredEffects.isEmpty())) {
            throw UserError.abort("-H:SideEffectAnalysisKillSets=%s partitions by field and leaves no effect out: -H:SideEffectAnalysisPartition and -H:SideEffectAnalysisIgnoreEffects need the tool",
                            killSetsBy);
        }
        boolean written = !(narrow && killSetsBy.equals("build")) || elideLocks || graphs;
        if (!written) {
            // Not this build's: nothing may read an export an earlier build left here.
            Files.deleteIfExists(export);
        }
        Set<String> assumed = assumptions.isEmpty() ? PointsToExport.defaultAssumptions() : Set.of(assumptions.split(","));
        List<String> worked = PointsToExport.export((PointsToAnalysis) access.getBigBang(), access.getUniverse(), written && !graphs ? export.toString() : "",
                        written && graphs ? export.toString() : "", null, true, program, threadEscape, assumed, inBuild);
        times.time("export", start);
        PointsToExport.STEP_NANOS.forEach((step, stepNanos) -> times.add("export: " + step, stepNanos));
        exportBytes = written ? Files.size(export) : 0;
        return worked;
    }

    /** Runs effects.elide on the export, and reads the monitors and volatile accesses it says can go. */
    private void readLockDecisions(Path export) throws IOException, InterruptedException {
        Path locks = out.resolve("locks.txt");
        runTool("effects.elide", export, export.toString(), "-o", locks.toString());
        lockElision.read(locks);
    }

    /**
     * Reads what each method may write, as the build worked it out ({@code worked}) or as
     * effects.kills says from the export, with objects told apart each access's partition too. With
     * both, the build stops if the two differ.
     */
    private void readKillSets(Path export, List<String> worked) throws IOException, InterruptedException {
        Path kills = out.resolve("kills.txt");
        if (killSetsBy.equals("build")) {
            // What the tool would have written, for what reads kills.txt after the build.
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

    /**
     * Stops the build if a method's kill set worked out in the build is not the tool's, and leaves
     * the build's in kills-build.txt next to the tool's kills.txt.
     */
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

    /** Lines of kills.txt by method: what follows the tab. */
    private static Map<String, String> byMethod(List<String> lines) {
        Map<String, String> byMethod = new HashMap<>();
        for (String line : lines) {
            int tab = line.indexOf('\t');
            byMethod.put(line.substring(0, tab), line.substring(tab + 1));
        }
        return byMethod;
    }

    /**
     * Runs a module of the tool on the export, {@code python -m module arguments}, as a step of
     * the analysis.
     */
    private void runTool(String module, Path export, String... arguments) throws IOException, InterruptedException {
        List<String> command = new ArrayList<>(List.of(Options.SideEffectAnalysisUv.getValue(), "run", "--project", Options.SideEffectAnalysisTool.getValue(), "python", "-m", module));
        command.addAll(List.of(arguments));
        long start = System.nanoTime();
        runToEnd(new ProcessBuilder(command), module, export);
        times.time(module, start);
    }

    /**
     * Runs a tool of the analysis to its end and stops it, with the processes it started, when the
     * image generator ends first: the generator's watchdog aborts a build whose step takes ten
     * minutes (-H:DeadlockWatchdogInterval), and a tool left running would go on using the
     * machine's memory.
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
                // the generator is already ending: the hook runs
            }
        }
    }

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
                 * After Native Image's inliners, where it puts RemoveUnwindPhase, so that the calls
                 * and stores that inlining brings into a method get the analysis too. Before them
                 * only canonicalization runs, which no kill set changes.
                 */
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

    @Override
    public void afterCompilation(AfterCompilationAccess access) {
        try {
            Files.createDirectories(out);
            counts.write(out, label);
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
            Files.writeString(out.resolve("timings.txt"), timings);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private static List<String> prefixes(String commaSeparated) {
        return Arrays.stream(commaSeparated.split(",")).filter(prefix -> !prefix.isEmpty()).toList();
    }
}
