package com.oracle.svm.hosted.sideeffects;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.ListIterator;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.LongAdder;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.graalvm.word.LocationIdentity;

import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.export.PointsToExport;
import com.oracle.svm.core.deopt.DeoptimizationSupport;
import com.oracle.svm.core.feature.InternalFeature;
import com.oracle.svm.core.graal.phases.RemoveUnwindPhase;
import com.oracle.svm.core.graal.snippets.SubstrateAllocationSnippets;
import com.oracle.svm.core.thread.SafepointCheckCounter;
import com.oracle.svm.core.util.UserError;
import com.oracle.svm.hosted.FeatureImpl;
import com.oracle.svm.hosted.meta.HostedField;
import com.oracle.svm.hosted.meta.HostedMethod;
import com.oracle.svm.shared.feature.AutomaticallyRegisteredFeature;
import com.oracle.svm.shared.option.HostedOptionKey;

import jdk.graal.compiler.core.common.memory.MemoryOrderMode;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.graph.NodeSourcePosition;
import jdk.graal.compiler.nodes.AbstractDeoptimizeNode;
import jdk.graal.compiler.nodes.ControlSplitNode;
import jdk.graal.compiler.nodes.FieldLocationIdentity;
import jdk.graal.compiler.nodes.FixedNode;
import jdk.graal.compiler.nodes.GraphState;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.InvokeWithExceptionNode;
import jdk.graal.compiler.nodes.NamedLocationIdentity;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.cfg.ControlFlowGraph;
import jdk.graal.compiler.nodes.cfg.HIRBlock;
import jdk.graal.compiler.nodes.extended.OSRMonitorEnterNode;
import jdk.graal.compiler.nodes.java.AccessFieldNode;
import jdk.graal.compiler.nodes.java.AccessMonitorNode;
import jdk.graal.compiler.nodes.java.ExceptionObjectNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.java.MonitorEnterNode;
import jdk.graal.compiler.nodes.java.MonitorExitNode;
import jdk.graal.compiler.nodes.java.MonitorIdNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.memory.AbstractWriteNode;
import jdk.graal.compiler.nodes.memory.FloatingReadNode;
import jdk.graal.compiler.nodes.memory.MemoryAccess;
import jdk.graal.compiler.nodes.memory.ReadNode;
import jdk.graal.compiler.nodes.util.GraphUtil;
import jdk.graal.compiler.options.Option;
import jdk.graal.compiler.options.OptionStability;
import jdk.graal.compiler.phases.BasePhase;
import jdk.graal.compiler.phases.Phase;
import jdk.graal.compiler.phases.common.OverwrittenStoreEliminationPhase;
import jdk.graal.compiler.phases.tiers.HighTierContext;
import jdk.graal.compiler.phases.tiers.Suites;
import jdk.graal.compiler.phases.util.Providers;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Applies a side-effect analysis to the image's compilation, in one native-image build. After the
 * points-to analysis, the feature exports its results ({@link PointsToExport}) and runs the
 * explicit-effects tool on them (effects.kills), which says what each method, with everything it
 * calls, may write. Right after Native Image inlines, every call in the program's methods, the
 * inlined ones included, kills only those locations instead of all of memory, and Graal's own
 * phases do the rest. The tool can also give each access to a field the location of its partition
 * of the objects. A phase at the end of the low tier counts the field stores, field loads and calls
 * left in the program's methods, and timings.txt records what each step of the analysis cost in
 * the build.
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
    private final boolean vm = Options.SideEffectAnalysisKillVMState.getValue();
    private final boolean platform = Options.SideEffectAnalysisKillPlatformFields.getValue();
    private final List<String> only = prefixes(Options.SideEffectAnalysisOnlyMethods.getValue());
    private final List<String> skip = prefixes(Options.SideEffectAnalysisSkipMethods.getValue());
    private final String label = !Options.SideEffectAnalysisLabel.getValue().isEmpty() ? Options.SideEffectAnalysisLabel.getValue()
                    : !narrow ? "graal" : overwrittenStores ? "graal-dse" : partition.equals("field") ? "fields" : "objects";

    /**
     * Method name and descriptor -> the partitions it may write; absent: anything.
     */
    private final Map<String, List<String>> written = new HashMap<>();
    /**
     * Where an access is, a tab, and its field -> its partition.
     */
    private final Map<String, String> located = new HashMap<>();
    /**
     * Where a monitor the tool says can go is, a tab, and enter or exit.
     */
    private final Map<String, String> elide = new HashMap<>();
    private final AtomicInteger monitorsRemoved = new AtomicInteger();
    private final AtomicInteger locksRemoved = new AtomicInteger();
    private final AtomicInteger locksKeptForDeoptimization = new AtomicInteger();
    private final AtomicInteger volatilesMadePlain = new AtomicInteger();
    /**
     * The image's fields by name, to give Graal's locations for the partitions.
     */
    private final Map<String, HostedField> fields = new HashMap<>();
    /**
     * The VM's state every narrowed call kills: see the class comment.
     */
    private final List<LocationIdentity> vmState = new ArrayList<>();
    /**
     * What the low tier leaves of each of the program's methods, and what the phases changed in
     * it: the calls narrowed, the fields partitioned, the monitors and stores removed.
     */
    private final Map<String, String> counts = new ConcurrentHashMap<>();
    private final Map<String, List<String>> narrowed = new ConcurrentHashMap<>();
    /**
     * What the low tier leaves of each of the program's methods in control flow (control.txt), and
     * where each field load and store left in it is, with the inlining it came through and whether
     * it is in a loop (sites.txt).
     */
    private final Map<String, String> control = new ConcurrentHashMap<>();
    private final Map<String, List<String>> sites = new ConcurrentHashMap<>();
    /**
     * What each of the program's methods looks like at the end of the low tier apart from the loads
     * and stores left in it, for measuring without the inlining and the unrolling in the way
     * (shape.txt).
     */
    private final Map<String, String> shape = new ConcurrentHashMap<>();
    /**
     * The call sites each of the program's methods had inlined into it, as callee < caller@bci <
     * ... (inlined.txt), for telling a load that is gone from one that was never inlined into the
     * method.
     */
    private final Map<String, TreeSet<String>> inlinedSites = new ConcurrentHashMap<>();
    /**
     * The address at the end of a hidden class's name changes from build to build; the content hash
     * before it does not.
     */
    private static final Pattern HIDDEN_CLASS_ADDRESS = Pattern.compile("/0x[0-9a-f]+");
    /**
     * What each step of the analysis cost in this build, in nanoseconds, and how often it ran: the
     * export and the tool once, each phase once per graph, summed over the compiler's threads.
     * Written to timings.txt, with the size of the export.
     */
    private final Map<String, LongAdder> nanos = new ConcurrentHashMap<>();
    private final Map<String, LongAdder> runs = new ConcurrentHashMap<>();
    private long exportBytes;
    private long methodsWithFacts;

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
            export((FeatureImpl.AfterAnalysisAccessImpl) access, export);
            if (elideLocks) {
                readLockDecisions(export);
            }
            if (!narrow) {
                return;
            }
            readKillSets(export);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        } catch (InterruptedException e) {
            throw new IllegalStateException(e);
        }
        String lie = Options.SideEffectAnalysisClaimWritesNothing.getValue();
        if (!lie.isEmpty()) {
            written.put(lie, List.of());
        }
    }

    /** Exports what the points-to analysis found, and adds what its steps cost to the timings. */
    private void export(FeatureImpl.AfterAnalysisAccessImpl access, Path export) throws IOException {
        long start = System.nanoTime();
        String assumptions = Options.SideEffectAnalysisAssumptions.getValue();
        if (!threadEscape && (elideLocks || !assumptions.isEmpty() || !Options.SideEffectAnalysisClaimLocksLocal.getValue().isEmpty())) {
            throw UserError.abort("-H:-SideEffectAnalysisThreadEscape leaves out what -H:+SideEffectAnalysisElideLocks, -H:SideEffectAnalysisAssumptions and -H:SideEffectAnalysisClaimLocksLocal need");
        }
        PointsToExport.THREAD_ESCAPE = threadEscape;
        if (!assumptions.isEmpty()) {
            PointsToExport.ASSUMPTIONS = Set.of(assumptions.split(","));
        }
        PointsToExport.export((PointsToAnalysis) access.getBigBang(), access.getUniverse(), graphs ? "" : export.toString(), graphs ? export.toString() : "", null, true, program);
        time("export", start);
        PointsToExport.STEP_NANOS.forEach((step, stepNanos) -> {
            nanos.computeIfAbsent("export: " + step, k -> new LongAdder()).add(stepNanos);
            runs.computeIfAbsent("export: " + step, k -> new LongAdder()).increment();
        });
        exportBytes = Files.size(export);
    }

    /** Runs effects.elide on the export, and reads the monitors and volatile accesses it says can go. */
    private void readLockDecisions(Path export) throws IOException, InterruptedException {
        Path monitors = out.resolve("locks.txt");
        runTool("effects.elide", export, export.toString(), "-o", monitors.toString());
        for (String line : Files.readAllLines(monitors)) {
            String[] parts = line.split("\t", 2);
            elide.put(parts[0], parts[1]);
        }
    }

    /** Runs effects.kills on the export, and reads what each method may write and, with objects told apart, each access's partition. */
    private void readKillSets(Path export) throws IOException, InterruptedException {
        Path answer = out.resolve("kills.txt");
        Path partitions = out.resolve("accesses.txt");
        List<String> arguments = new ArrayList<>(List.of(export.toString(), "-o", answer.toString(), "--partition", partition));
        if (!partition.equals("field")) {
            arguments.addAll(List.of("--accesses", partitions.toString()));
        }
        if (!ignoredEffects.isEmpty()) {
            arguments.addAll(List.of("--ignore", ignoredEffects));
        }
        runTool("effects.kills", export, arguments.toArray(new String[0]));
        for (String line : Files.readAllLines(answer)) {
            methodsWithFacts++;
            String[] parts = line.split("\t", -1);
            if (!parts[1].equals("any")) {
                written.put(parts[0], parts[1].isEmpty() ? List.of() : List.of(parts[1].split(",")));
            }
        }
        if (!partition.equals("field")) {
            for (String line : Files.readAllLines(partitions)) {
                String[] parts = line.split("\t", -1);
                located.put(parts[0] + "\t" + parts[1], parts[2]);
            }
        }
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
        time(module, start);
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
        for (HostedField field : ((FeatureImpl.BeforeCompilationAccessImpl) access).getUniverse().getFields()) {
            fields.put(fieldName(field), field);
        }
        // What Native Image's safepoint kills (SafepointSnippets).
        vmState.addAll(List.of(SubstrateAllocationSnippets.GC_LOCATIONS));
        vmState.add(SafepointCheckCounter.getLocationIdentity());
        HostedField sessionState = fields.get("jdk.internal.foreign.MemorySessionImpl.state");
        if (sessionState != null) {
            vmState.add(new FieldLocationIdentity(sessionState));
        }
    }

    /**
     * Graal's locations for a partition the tool names: a field, an array kind, or with objects
     * told apart a field of a set of them, Aliasing$Counter.value@main:199. A field this graph
     * gives partitions is killed in its partition, and as a whole too, for the phases that key
     * field accesses by the field alone, such as read elimination; any other is killed whole.
     */
    private List<LocationIdentity> locations(String written, Set<String> partitioned) {
        if (written.equals("init")) {
            return List.of(); // the callee's own initialization: see the class comment
        }
        if (written.startsWith("vm:")) {
            LocationIdentity location = PointsToExport.VM_LOCATIONS.get(written);
            return !vm ? List.of() : location != null ? List.of(location) : null; // null: unnamed here, so anything
        }
        String whole = written.contains("@") ? written.substring(0, written.indexOf('@')) : written;
        if (whole.endsWith("[]")) {
            return arrayKinds(whole).stream().map(NamedLocationIdentity::getArrayLocation).toList();
        }
        HostedField field = fields.get(whole);
        if (field == null || (!platform && !PointsToExport.isProgramClass(field.getDeclaringClass().toJavaName(true), program))) {
            return List.of(); // the image never accesses it, so there is nothing to kill; or the control
        }
        return partitioned.contains(whole) ? List.of(new FieldLocationIdentity(field), new FieldLocationIdentity(field, false, written))
                        : List.of(new FieldLocationIdentity(field));
    }

    /**
     * The element kinds of an export's array partition: byte[] stands for boolean[] too.
     */
    private static List<JavaKind> arrayKinds(String partition) {
        return switch (partition) {
            case "byte[]" -> List.of(JavaKind.Byte, JavaKind.Boolean);
            case "Object[]" -> List.of(JavaKind.Object);
            default -> List.of(JavaKind.fromJavaClass(primitive(partition.substring(0, partition.length() - 2))));
        };
    }

    private static Class<?> primitive(String name) {
        return switch (name) {
            case "char" -> char.class;
            case "short" -> short.class;
            case "int" -> int.class;
            case "long" -> long.class;
            case "float" -> float.class;
            case "double" -> double.class;
            default -> throw new IllegalArgumentException("Not an array kind: " + name);
        };
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
                    phases.add(new ApplySideEffectAnalysisPhase());
                    if (overwrittenStores) {
                        phases.add(new EliminateOverwrittenStoresPhase());
                    }
                }
                if (elideLocks) {
                    phases.add(new ElideLocksPhase());
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
                suites.getMidTier().prependPhase(new VerifyFieldPartitionsPhase());
            }
            suites.getLowTier().appendPhase(new CountCompiledCodePhase());
        }
    }

    /**
     * Adds the time since {@code start} to a step of the analysis.
     */
    private void time(String step, long start) {
        nanos.computeIfAbsent(step, k -> new LongAdder()).add(System.nanoTime() - start);
        runs.computeIfAbsent(step, k -> new LongAdder()).increment();
    }

    @Override
    public void afterCompilation(AfterCompilationAccess access) {
        StringBuilder text = new StringBuilder();
        for (Map.Entry<String, String> method : new TreeMap<>(counts).entrySet()) {
            text.append(method.getKey()).append('\n').append(String.format("    %-10s %s%n", label, method.getValue()));
            for (String call : narrowed.getOrDefault(method.getKey(), List.of())) {
                text.append("        ").append(call).append('\n');
            }
        }
        try {
            Files.createDirectories(out);
            Files.writeString(out.resolve("counts.txt"), text);
            writeRows("control.txt", "# method\tblocks\tcontrol-flow edges\tifs\tswitches and other splits\tloops\tcalls with an exception edge\tdeoptimizations\n", control);
            writeRows("shape.txt", "# method\tnodes\tfixed nodes\tlongest path in blocks (back edges cut)\tlongest path in fixed nodes\tdeepest loop\tinlined call sites" +
                            "\tinlining hash (0 without -H:+TrackNodeSourcePosition)\tif places (each if once, however many copies unrolling made)\tcall places\tifs without a place\n", shape);
            writeLines("inlined.txt", "# method\tinlined call site: callee < caller@bci < ... (the callee is the method that was inlined; empty without -H:+TrackNodeSourcePosition)\n",
                            inlinedSites);
            writeLines("sites.txt", "# method\tload or store\tin a loop or not\tfield\tinlining it came through, innermost first (- without -H:+TrackNodeSourcePosition)\n", sites);
            StringBuilder timings = new StringBuilder("# step\tseconds\truns (the export and the tool once, a phase once per graph, summed over the compiler's threads)\n");
            for (Map.Entry<String, LongAdder> step : new TreeMap<>(nanos).entrySet()) {
                timings.append(String.format(Locale.ROOT, "%s\t%.3f\t%d%n", step.getKey(), step.getValue().sum() / 1e9, runs.get(step.getKey()).sum()));
            }
            timings.append(String.format("# export.json: %d bytes, %d methods with facts%n", exportBytes, methodsWithFacts));
            if (!ignoredEffects.isEmpty()) {
                timings.append(String.format("# the kill of %s is left out of the kill sets: an upper bound, not sound%n", ignoredEffects));
            }
            if (elideLocks) {
                timings.append(String.format("# locks removed: %d, with %d monitor enters and exits; volatile accesses made ordinary: %d; of %d sites the tool listed%n", locksRemoved.get(),
                                monitorsRemoved.get(), volatilesMadePlain.get(), elide.size()));
                timings.append(String.format("# locks kept because the image can deoptimize: %d%n", locksKeptForDeoptimization.get()));
            }
            Files.writeString(out.resolve("timings.txt"), timings);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /** Writes a table of one row for each method, in the order of their names, under its header. */
    private void writeRows(String file, String header, Map<String, String> rows) throws IOException {
        StringBuilder text = new StringBuilder(header);
        new TreeMap<>(rows).forEach((method, row) -> text.append(method).append('\t').append(row).append('\n'));
        Files.writeString(out.resolve(file), text);
    }

    /** Writes a table of any number of rows for each method, in the order of their names, under its header. */
    private void writeLines(String file, String header, Map<String, ? extends Collection<String>> lines) throws IOException {
        StringBuilder text = new StringBuilder(header);
        new TreeMap<>(lines).forEach((method, list) -> list.forEach(line -> text.append(method).append('\t').append(line).append('\n')));
        Files.writeString(out.resolve(file), text);
    }

    private boolean inProgram(ResolvedJavaMethod method) {
        return PointsToExport.isProgramClass(method.getDeclaringClass().toJavaName(true), program);
    }

    private static List<String> prefixes(String commaSeparated) {
        return Arrays.stream(commaSeparated.split(",")).filter(prefix -> !prefix.isEmpty()).toList();
    }

    /**
     * Whether the calls in a method are narrowed: the only and skip options limit it.
     */
    private boolean narrowsIn(ResolvedJavaMethod method) {
        String name = exportName(method);
        return (only.isEmpty() || only.stream().anyMatch(name::startsWith)) && skip.stream().noneMatch(name::startsWith);
    }

    /**
     * A method as the export names it: LoadStoreElimination.length(LLoadStoreElimination$Link;)I.
     */
    private static String exportName(ResolvedJavaMethod method) {
        return method.getDeclaringClass().toJavaName(true) + "." + method.getName() + method.getSignature().toMethodDescriptor();
    }

    /**
     * A method as the counts name it, for reading: LoadStoreElimination.length(Link).
     */
    private static String readableName(ResolvedJavaMethod method) {
        String parameters = IntStream.range(0, method.getSignature().getParameterCount(false))
                        .mapToObj(i -> simpleName(method.getSignature().getParameterType(i, null).toJavaName(true)))
                        .collect(Collectors.joining(", "));
        return method.getDeclaringClass().toJavaName(false) + "." + method.getName() + "(" + parameters + ")";
    }

    /** A field as the export names it: Aliasing$Counter.value. */
    private static String fieldName(ResolvedJavaField field) {
        return field.getDeclaringClass().toJavaName(true) + "." + field.getName();
    }

    /** A class's name without its package and the classes it is nested in. */
    private static String simpleName(String name) {
        return name.substring(Math.max(name.lastIndexOf('.'), name.lastIndexOf('$')) + 1);
    }

    /**
     * A field as the reports name it: Aliasing$Counter.value is Counter.value.
     */
    private static String shortField(String field) {
        int dot = field.lastIndexOf('.');
        return simpleName(field.substring(0, dot)) + field.substring(dot);
    }

    /**
     * What a call may write: the kills of every method it may call, null for anything.
     */
    private LocationIdentity[] killsOf(MethodCallTargetNode target, Set<String> partitioned) {
        HostedMethod method = (HostedMethod) target.targetMethod();
        HostedMethod[] callees = target.invokeKind().isDirect() ? new HostedMethod[]{method} : method.getImplementations();
        if (callees.length == 0) {
            return null;
        }
        List<LocationIdentity> all = new ArrayList<>();
        for (HostedMethod callee : callees) {
            List<String> partitions = written.get(exportName(callee));
            if (partitions == null) {
                return null;
            }
            for (String partitionWritten : partitions) {
                List<LocationIdentity> locations = locations(partitionWritten, partitioned);
                if (locations == null) {
                    return null;
                }
                all.addAll(locations);
            }
        }
        return all.toArray(new LocationIdentity[0]);
    }

    /**
     * The sites a node at {@code position} may be named by in the analysis's facts: its own, then
     * the same without each outermost caller in turn. A site names a node of the graph the facts
     * were taken from, innermost frame first (m:21 in c:4); inlining a copy of that graph into a
     * caller appends the caller's frame (m:21 in c:4 in h:7). A fact that holds in a graph holds
     * in every copy of it: an access's partition covers every context it is reached in.
     */
    private static List<String> sitesOf(String position) {
        List<String> sitesOfPosition = new ArrayList<>();
        String site = position;
        while (true) {
            sitesOfPosition.add(site);
            int outermost = site.lastIndexOf(" in ");
            if (outermost < 0) {
                return sitesOfPosition;
            }
            site = site.substring(0, outermost);
        }
    }

    /**
     * Whether the tool lists a node at {@code at} with this decision, or the control claims every
     * monitor and volatile access of its method local.
     */
    private boolean listedOrClaimed(String at, String decision) {
        String claimed = Options.SideEffectAnalysisClaimLocksLocal.getValue();
        return sitesOf(at).stream().anyMatch(site -> decision.equals(elide.get(site)) || !claimed.isEmpty() && site.startsWith(claimed + ":"));
    }

    /**
     * The reference an access goes through, for the split: a parameter, or any other value.
     */
    @SuppressWarnings("deprecation") // a node's id, only to tell values of this graph apart
    private static String reference(AccessFieldNode access) {
        return GraphUtil.unproxify(access.object()) instanceof ParameterNode parameter ? "param" + parameter.index() : "v" + access.object().getId();
    }

    /**
     * Gives each access to a field the location of its partition, when the facts give every
     * access to the field one, and reports the partitions each such field got.
     */
    private Set<String> partition(StructuredGraph graph, List<String> report) {
        boolean split = exportName(graph.method()).equals(Options.SideEffectAnalysisClaimNoAliasing.getValue());
        Map<String, List<AccessFieldNode>> byField = new TreeMap<>();
        for (AccessFieldNode access : graph.getNodes().filter(AccessFieldNode.class)) {
            byField.computeIfAbsent(fieldName(access.field()), k -> new ArrayList<>()).add(access);
        }
        Set<String> partitioned = new HashSet<>();
        for (Map.Entry<String, List<AccessFieldNode>> field : byField.entrySet()) {
            List<String> partitions = new ArrayList<>();
            for (AccessFieldNode access : field.getValue()) {
                String at = PointsToExport.position(access.getNodeSourcePosition());
                String found = at == null || access.getLocationIdentity().isImmutable() || access.ordersMemoryAccesses() ? null
                                : sitesOf(at).stream().map(site -> located.get(site + "\t" + field.getKey())).filter(Objects::nonNull).findFirst().orElse(null);
                partitions.add(found == null || !split ? found : found + "#" + reference(access));
            }
            if (partitions.contains(null) || partitions.stream().allMatch(field.getKey()::equals)) {
                continue;
            }
            for (int i = 0; i < partitions.size(); i++) {
                field.getValue().get(i).setLocationIdentity(new FieldLocationIdentity(field.getValue().get(i).field(), false, partitions.get(i)));
            }
            partitioned.add(field.getKey());
            report.add(String.format("%s in %s", shortField(field.getKey()),
                            new TreeSet<>(partitions).stream().map(p -> p.contains("@") ? p.substring(p.indexOf('@')) : p).collect(Collectors.joining(" "))));
        }
        return partitioned;
    }

    /**
     * Adds what a phase changed in a method to what the counts list under it, in sorted order.
     */
    private void report(StructuredGraph graph, List<String> changes) {
        narrowed.merge(readableName(graph.method()), changes, (before, more) -> {
            List<String> all = new ArrayList<>(before);
            all.addAll(more);
            Collections.sort(all);
            return all;
        });
    }

    /**
     * A phase of this feature: it applies to every graph, and the time it takes is added to its step
     * in timings.txt.
     */
    private abstract class TimedPhase extends Phase {
        private final String step;

        TimedPhase(String step) {
            this.step = step;
        }

        @Override
        public Optional<NotApplicable> notApplicableTo(GraphState graphState) {
            return ALWAYS_APPLICABLE;
        }

        @Override
        protected final void run(StructuredGraph graph) {
            long start = System.nanoTime();
            try {
                runOn(graph);
            } finally {
                time(step, start);
            }
        }

        protected abstract void runOn(StructuredGraph graph);
    }

    /**
     * Applies the analysis to one of the program's methods, right after Native Image's inliners:
     * gives accesses their partitions, and narrows each call, and the entry of its exception
     * handler, to what its callees may write. Inlined code included: a call's kill set belongs to
     * its targets, not to where the call is.
     */
    private final class ApplySideEffectAnalysisPhase extends TimedPhase {
        ApplySideEffectAnalysisPhase() {
            super("apply");
        }

        @Override
        protected void runOn(StructuredGraph graph) {
            if (!inProgram(graph.method())) {
                return;
            }
            List<String> calls = new ArrayList<>();
            Set<String> partitioned = located.isEmpty() ? Set.of() : partition(graph, calls);
            boolean narrows = narrowsIn(graph.method());
            for (Node node : graph.getNodes()) {
                if (narrows && node instanceof Invoke invoke && invoke.callTarget() instanceof MethodCallTargetNode target) {
                    LocationIdentity[] locations = killsOf(target, partitioned);
                    if (locations != null) {
                        List<LocationIdentity> killed = new ArrayList<>(List.of(locations));
                        if (vm) {
                            killed.addAll(vmState);
                        }
                        invoke.setKilledLocationIdentities(killed.toArray(new LocationIdentity[0]));
                        if (invoke instanceof InvokeWithExceptionNode withException && withException.exceptionEdge() instanceof ExceptionObjectNode handler) {
                            // The handler is entered after the callee threw: before it did, it may
                            // have written what it writes otherwise.
                            handler.setKilledLocationIdentities(killed.toArray(new LocationIdentity[0]));
                        }
                        LocationIdentity[] set = Invoke.killSet(Arrays.stream(locations).filter(l -> !vmState.contains(l)).toArray(LocationIdentity[]::new));
                        calls.add(String.format("%s kills %s", readableName(target.targetMethod()), set.length == 0 ? "nothing"
                                        : Arrays.stream(set).map(l -> simpleName(l.toString())).collect(Collectors.joining(" "))));
                    }
                }
            }
            if (!calls.isEmpty()) {
                Collections.sort(calls);
                narrowed.put(readableName(graph.method()), calls);
            }
            graph.getDebug().dump(DebugContext.BASIC_LEVEL, graph, "After applying the side-effect analysis");
        }
    }

    /**
     * Removes the monitor enters and exits the tool says are on objects only one thread reaches, in
     * every method, inlined code included. A lock goes whole or not at all: its enter and every
     * exit, the ones on the paths that throw too, must all be listed, or the frame states and the
     * monitors left would not match. Positions need -H:+TrackNodeSourcePosition.
     * <p>
     * An image that can deoptimize keeps its monitors. Code compiled while the program runs does
     * not pass through this phase and takes the locks it finds; when it is deoptimized inside a
     * locked region, its frame goes on in the version of the method the image was built with, and
     * that version must release the lock the compiled code took. Without its monitors it would not,
     * and the thread would hold the lock for good. The volatile accesses are not affected.
     */
    private final class ElideLocksPhase extends TimedPhase {
        ElideLocksPhase() {
            super("elide locks");
        }

        @Override
        protected void runOn(StructuredGraph graph) {
            List<String> removed = new ArrayList<>();
            makeVolatilesPlain(graph, removed);
            List<AccessMonitorNode> monitors = graph.getNodes().filter(AccessMonitorNode.class).snapshot();
            Map<MonitorIdNode, List<AccessMonitorNode>> locks = new HashMap<>();
            for (AccessMonitorNode monitor : monitors) {
                locks.computeIfAbsent(monitor.getMonitorId(), k -> new ArrayList<>()).add(monitor);
            }
            boolean deoptimizes = DeoptimizationSupport.enabled() && !Options.SideEffectAnalysisClaimNoDeoptimization.getValue();
            for (List<AccessMonitorNode> lock : locks.values()) {
                if (lock.stream().allMatch(this::listed)) {
                    if (deoptimizes) {
                        locksKeptForDeoptimization.incrementAndGet();
                        continue;
                    }
                    for (AccessMonitorNode monitor : lock) {
                        removed.add(String.format("monitor %s at bci %d removed", monitor instanceof MonitorEnterNode ? "enter" : "exit",
                                        monitor.getNodeSourcePosition() != null ? monitor.getNodeSourcePosition().getBCI() : -1));
                        GraphUtil.removeFixedWithUnusedInputs(monitor);
                    }
                    monitorsRemoved.addAndGet(lock.size());
                    locksRemoved.incrementAndGet();
                }
            }
            if (!removed.isEmpty()) {
                report(graph, removed);
                graph.getDebug().dump(DebugContext.BASIC_LEVEL, graph, "After eliminating locks");
            }
        }

        /**
         * A volatile access of a field the tool says only one thread reaches orders nothing: it
         * becomes an ordinary one.
         */
        private void makeVolatilesPlain(StructuredGraph graph, List<String> report) {
            for (AccessFieldNode access : graph.getNodes().filter(AccessFieldNode.class).snapshot()) {
                if (access.getMemoryOrder() != MemoryOrderMode.VOLATILE) {
                    continue;
                }
                String at = PointsToExport.position(access.getNodeSourcePosition());
                if (at == null) {
                    continue;
                }
                if (listedOrClaimed(at, (access instanceof LoadFieldNode ? "plain-read" : "plain-write") + "\t" + fieldName(access.field()))) {
                    access.makePlain();
                    volatilesMadePlain.incrementAndGet();
                    report.add(String.format("volatile %s of %s at bci %d made ordinary", access instanceof LoadFieldNode ? "read" : "write", shortField(fieldName(access.field())),
                                    access.getNodeSourcePosition().getBCI()));
                }
            }
        }

        private boolean listed(AccessMonitorNode monitor) {
            String kind = monitor instanceof MonitorEnterNode && !(monitor instanceof OSRMonitorEnterNode) ? "enter" : monitor instanceof MonitorExitNode ? "exit" : null;
            String at = PointsToExport.position(monitor.getNodeSourcePosition());
            if (kind == null || at == null) {
                return false;
            }
            return listedOrClaimed(at, kind);
        }
    }

    /**
     * Runs Graal's {@link OverwrittenStoreEliminationPhase} on one of the program's methods, after
     * the analysis is applied (so with its partitions), and reports each store it removes.
     */
    private final class EliminateOverwrittenStoresPhase extends TimedPhase {
        EliminateOverwrittenStoresPhase() {
            super("eliminate overwritten stores");
        }

        @Override
        protected void runOn(StructuredGraph graph) {
            if (!inProgram(graph.method())) {
                return;
            }
            List<String> removed = new ArrayList<>();
            for (StoreFieldNode store : OverwrittenStoreEliminationPhase.overwrittenStores(graph)) {
                removed.add(String.format("overwritten store to %s at bci %d removed", shortField(fieldName(store.field())),
                                store.getNodeSourcePosition() != null ? store.getNodeSourcePosition().getBCI() : -1));
                GraphUtil.removeFixedWithUnusedInputs(store);
            }
            if (!removed.isEmpty()) {
                report(graph, removed);
            }
            graph.getDebug().dump(DebugContext.BASIC_LEVEL, graph, "After eliminating overwritten stores");
        }
    }

    /**
     * Stops the build if a graph has accesses to one field both with and without a partition, as
     * a phase that makes a new access after the partitioning could: their locations would not
     * overlap, and nothing would order them.
     */
    private final class VerifyFieldPartitionsPhase extends TimedPhase {
        VerifyFieldPartitionsPhase() {
            super("verify partitions");
        }

        @Override
        protected void runOn(StructuredGraph graph) {
            Map<ResolvedJavaField, Set<Boolean>> kinds = new HashMap<>();
            for (Node node : graph.getNodes()) {
                if (node instanceof MemoryAccess access && access.getLocationIdentity() instanceof FieldLocationIdentity field && !field.isImmutable()) {
                    kinds.computeIfAbsent(field.getField(), k -> new HashSet<>()).add(field.getPartition() != null);
                }
            }
            kinds.forEach((field, partitioned) -> {
                if (partitioned.size() > 1) {
                    throw new IllegalStateException(graph.method().format("%H.%n") + " accesses " + fieldName(field) + " both with and without a partition");
                }
            });
        }
    }

    /**
     * Records what the low tier leaves of one of the program's methods: its calls, field stores and
     * field loads (counts.txt), its control flow (control.txt), where each access is (sites.txt),
     * the size and the paths of its graph and the inlining it was built from (shape.txt,
     * inlined.txt). Measurement only: it changes nothing.
     */
    private final class CountCompiledCodePhase extends TimedPhase {
        CountCompiledCodePhase() {
            super("count accesses (measurement only)");
        }

        @Override
        protected void runOn(StructuredGraph graph) {
            if (!inProgram(graph.method())) {
                return;
            }
            ControlFlowGraph cfg = ControlFlowGraph.newBuilder(graph).connectBlocks(true).computeLoops(true).build();
            Map<String, Integer> writes = new TreeMap<>();
            Map<String, Integer> reads = new TreeMap<>();
            List<String> accessSites = new ArrayList<>();
            int calls = 0;
            int ifs = 0;
            int otherSplits = 0;
            int exceptionCalls = 0;
            int deoptimizations = 0;
            for (Node node : graph.getNodes()) {
                if (node instanceof Invoke) {
                    calls++;
                } else if (node instanceof MemoryAccess access && access.getLocationIdentity() instanceof FieldLocationIdentity field) {
                    HIRBlock block = cfg.blockFor(node);
                    boolean loop = block != null && block.getLoop() != null;
                    String where = simpleName(field.getField().format("%H")) + "." + field.getField().getName() + (loop ? "(loop)" : "");
                    boolean store = node instanceof StoreFieldNode || node instanceof AbstractWriteNode;
                    Map<String, Integer> counted = store ? writes
                                    : node instanceof LoadFieldNode || node instanceof ReadNode || node instanceof FloatingReadNode ? reads : null;
                    if (counted != null) {
                        counted.merge(where, 1, Integer::sum);
                        accessSites.add(String.join("\t", store ? "store" : "load", loop ? "loop" : "flat", simpleName(field.getField().format("%H")) + "." + field.getField().getName(),
                                        position(node)));
                    }
                }
                if (node instanceof InvokeWithExceptionNode) {
                    exceptionCalls++;
                } else if (node instanceof IfNode) {
                    ifs++;
                } else if (node instanceof ControlSplitNode) {
                    otherSplits++;
                } else if (node instanceof AbstractDeoptimizeNode) {
                    deoptimizations++;
                }
            }
            String method = readableName(graph.method());
            counts.put(method, String.format("calls %d   writes %-32s reads %s", calls, show(writes), show(reads)));
            int edges = 0;
            for (HIRBlock block : cfg.getBlocks()) {
                edges += block.getSuccessorCount();
            }
            control.put(method, String.join("\t", Integer.toString(cfg.getBlocks().length), Integer.toString(edges), Integer.toString(ifs), Integer.toString(otherSplits),
                            Integer.toString(cfg.getLoops().size()), Integer.toString(exceptionCalls), Integer.toString(deoptimizations)));
            accessSites.sort(null);
            sites.put(method, accessSites);
            TreeSet<String> inlined = inlinedCallSites(graph);
            inlinedSites.put(method, inlined);
            shape.put(method, shapeOf(graph, cfg, inlined));
        }

        /**
         * The call sites inlined into a graph, as callee < caller@bci < ..., each once: every frame
         * of a node's position but the outermost is a method inlined at its caller's bci.
         */
        private static TreeSet<String> inlinedCallSites(StructuredGraph graph) {
            TreeSet<String> inlined = new TreeSet<>();
            for (Node node : graph.getNodes()) {
                NodeSourcePosition position = node.getNodeSourcePosition();
                if (position == null) {
                    continue;
                }
                for (NodeSourcePosition frame = position; frame.getCaller() != null; frame = frame.getCaller()) {
                    StringBuilder callSite = new StringBuilder(readableName(frame.getMethod()));
                    for (NodeSourcePosition caller = frame.getCaller(); caller != null; caller = caller.getCaller()) {
                        callSite.append(" < ").append(readableName(caller.getMethod())).append('@').append(caller.getBCI());
                    }
                    inlined.add(HIDDEN_CLASS_ADDRESS.matcher(callSite).replaceAll("/0xH"));
                }
            }
            return inlined;
        }

        /**
         * The graph's size (nodes, fixed nodes), the longest path through its control flow with the
         * back edges cut (in blocks and in fixed nodes), its deepest loop, and the inlining it was
         * built from: the number of distinct inlined call sites and a hash of them, so that two
         * methods with the same inlining can be told from two that differ in it (0 and 0 without
         * -H:+TrackNodeSourcePosition).
         */
        private static String shapeOf(StructuredGraph graph, ControlFlowGraph cfg, TreeSet<String> inlined) {
            HIRBlock[] blocks = cfg.getBlocks();
            Map<HIRBlock, Integer> order = new IdentityHashMap<>();
            for (int i = 0; i < blocks.length; i++) {
                order.put(blocks[i], i);
            }
            int[] blocksBefore = new int[blocks.length];
            int[] fixedBefore = new int[blocks.length];
            int fixedNodes = 0;
            int longestInBlocks = 0;
            int longestInFixedNodes = 0;
            int deepestLoop = 0;
            for (int i = 0; i < blocks.length; i++) {
                int weight = 0;
                for (FixedNode ignored : blocks[i].getNodes()) {
                    weight++;
                }
                fixedNodes += weight;
                deepestLoop = Math.max(deepestLoop, blocks[i].getLoopDepth());
                int throughBlocks = blocksBefore[i] + 1;
                int throughFixedNodes = fixedBefore[i] + weight;
                longestInBlocks = Math.max(longestInBlocks, throughBlocks);
                longestInFixedNodes = Math.max(longestInFixedNodes, throughFixedNodes);
                for (int s = 0; s < blocks[i].getSuccessorCount(); s++) {
                    int successor = order.get(blocks[i].getSuccessorAt(s));
                    if (successor > i) { // forward edges only: the back edges of loops are cut
                        blocksBefore[successor] = Math.max(blocksBefore[successor], throughBlocks);
                        fixedBefore[successor] = Math.max(fixedBefore[successor], throughFixedNodes);
                    }
                }
            }
            TreeSet<String> ifPlaces = new TreeSet<>();
            TreeSet<String> callPlaces = new TreeSet<>();
            int ifsWithoutPlace = 0;
            for (Node node : graph.getNodes()) {
                NodeSourcePosition position = node.getNodeSourcePosition();
                if (node instanceof IfNode) {
                    if (position == null) {
                        ifsWithoutPlace++;
                    } else {
                        ifPlaces.add(position(node));
                    }
                } else if (node instanceof Invoke && position != null) {
                    callPlaces.add(position(node));
                }
            }
            String hash = "0";
            if (!inlined.isEmpty()) {
                try {
                    byte[] digest = MessageDigest.getInstance("SHA-256").digest(String.join("\n", inlined).getBytes(StandardCharsets.UTF_8));
                    hash = String.format("%02x%02x%02x%02x", digest[0], digest[1], digest[2], digest[3]);
                } catch (NoSuchAlgorithmException e) {
                    throw new IllegalStateException(e);
                }
            }
            return String.join("\t", Integer.toString(graph.getNodeCount()), Integer.toString(fixedNodes), Integer.toString(longestInBlocks), Integer.toString(longestInFixedNodes),
                            Integer.toString(deepestLoop), Integer.toString(inlined.size()), hash, Integer.toString(ifPlaces.size()), Integer.toString(callPlaces.size()),
                            Integer.toString(ifsWithoutPlace));
        }

        /**
         * The inlining a node came through, innermost first, as method@bci: the same field access
         * inlined at two call sites is two places. {@code -} where the compilation does not keep
         * source positions (-H:+TrackNodeSourcePosition).
         */
        private static String position(Node node) {
            NodeSourcePosition position = node.getNodeSourcePosition();
            if (position == null) {
                return "-";
            }
            StringBuilder chain = new StringBuilder();
            for (NodeSourcePosition at = position; at != null; at = at.getCaller()) {
                chain.append(chain.length() == 0 ? "" : " < ").append(readableName(at.getMethod())).append('@').append(at.getBCI());
            }
            return chain.toString();
        }

        private static String show(Map<String, Integer> counted) {
            return counted.isEmpty() ? "-"
                            : counted.entrySet().stream().map(e -> e.getKey() + (e.getValue() > 1 ? "\u00d7" + e.getValue() : "")).collect(Collectors.joining(" "));
        }
    }
}
