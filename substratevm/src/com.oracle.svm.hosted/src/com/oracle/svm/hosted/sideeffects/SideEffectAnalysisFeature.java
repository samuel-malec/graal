package com.oracle.svm.hosted.sideeffects;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Collectors;

import org.graalvm.word.LocationIdentity;

import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.export.PointsToExport;
import com.oracle.svm.core.feature.InternalFeature;
import com.oracle.svm.core.graal.phases.RemoveUnwindPhase;
import com.oracle.svm.hosted.FeatureImpl;
import com.oracle.svm.hosted.meta.HostedField;
import com.oracle.svm.hosted.meta.HostedMethod;
import com.oracle.svm.shared.feature.AutomaticallyRegisteredFeature;
import com.oracle.svm.shared.option.HostedOptionKey;

import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.FieldLocationIdentity;
import jdk.graal.compiler.nodes.GraphState;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.InvokeWithExceptionNode;
import jdk.graal.compiler.nodes.NamedLocationIdentity;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.cfg.ControlFlowGraph;
import jdk.graal.compiler.nodes.cfg.HIRBlock;
import jdk.graal.compiler.nodes.java.AccessFieldNode;
import jdk.graal.compiler.nodes.java.ExceptionObjectNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.memory.AbstractWriteNode;
import jdk.graal.compiler.nodes.memory.FloatingReadNode;
import jdk.graal.compiler.nodes.memory.MemoryAccess;
import jdk.graal.compiler.nodes.memory.ReadNode;
import jdk.graal.compiler.options.Option;
import jdk.graal.compiler.options.OptionStability;
import jdk.graal.compiler.phases.BasePhase;
import jdk.graal.compiler.phases.Phase;
import jdk.graal.compiler.phases.common.OverwrittenStoreEliminationPhase;
import jdk.graal.compiler.phases.tiers.HighTierContext;
import jdk.graal.compiler.phases.tiers.Suites;
import jdk.graal.compiler.phases.util.Providers;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Applies a side-effect analysis to the image's compilation, in one native-image build. After the
 * points-to analysis, the feature exports its results ({@link PointsToExport}) and runs the
 * explicit-effects tool on them (effects.kills), which says what each method, with everything it
 * calls, may write. Right after Native Image inlines, every call in the program's methods, the
 * inlined ones included, kills only those locations instead of all of memory, and Graal's own
 * phases do the rest. The tool can also give
 * each access to a field the location of its partition of the objects, and name stores that are
 * dead in Java. A phase at the end of the low tier counts the field stores, field loads and calls
 * left in the program's methods.
 *
 * Enabled with {@code -H:+SideEffectAnalysis}; the other options are in {@link Options}. With
 * {@code -H:Dump=:1}, the graph is dumped right after the analysis is applied, titled "After
 * applying the side-effect analysis".
 *
 * Every narrowed call also kills what a safepoint in its callees may change, as Native Image's
 * own safepoints do (the thread's allocation buffer, which a collection resets), and the
 * initialization of what they allocate: Native Image lowers an allocation after the memory graph
 * is built, so its read of the buffer would otherwise come from before the call.
 */
@AutomaticallyRegisteredFeature
public final class SideEffectAnalysisFeature implements InternalFeature {

    public static final class Options {
        @Option(help = "Apply a side-effect analysis (the explicit-effects tool) to the compilation: narrow what each call kills, and optionally partition field locations and remove dead stores.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysis = new HostedOptionKey<>(false);

        @Option(help = "The explicit-effects checkout whose tool computes the side effects; it runs with uv.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisTool = new HostedOptionKey<>(".");

        @Option(help = "The uv executable that runs the side-effect tool, as the builder's environment may not find it.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisUv = new HostedOptionKey<>("uv");

        @Option(help = "Directory for the exported points-to results, the tool's answers and the counts of what Graal leaves.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisOutput = new HostedOptionKey<>("side-effect-analysis");

        @Option(help = "Comma-separated class-name prefixes of the program whose calls are narrowed and whose accesses are counted. Empty: every class outside the platform's packages.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisProgram = new HostedOptionKey<>("");

        @Option(help = "Narrow what each call kills. Off, the feature only counts what Graal leaves, as a baseline.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisNarrowCalls = new HostedOptionKey<>(true);

        @Option(help = "How finely memory is partitioned: field keeps Graal's locations; object-field also splits each field by the sets of objects points-to analysis tells apart, which needs -H:AnalysisContextSensitivity=allocsens and -H:+TrackNodeSourcePosition.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisPartition = new HostedOptionKey<>("field");

        @Option(help = "Also remove the stores the tool's rules find dead in Java (rules.decisions), before Graal compiles.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisRemoveDeadStores = new HostedOptionKey<>(false);

        @Option(help = "Also run Graal's OverwrittenStoreEliminationPhase on the program's methods, right after the analysis is applied, so that its dead stores can be compared with the tool's decisions.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<Boolean> SideEffectAnalysisEliminateOverwrittenStores = new HostedOptionKey<>(false);

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

        @Option(help = "Control: a method in which different references are claimed never to meet, as an unsound points-to analysis would, so that a wrong partition shows in the output.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisClaimNoAliasing = new HostedOptionKey<>("");

        @Option(help = "Control: a position, method:bci, whose stores are claimed dead, so that a wrong decision shows in the output.", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisClaimDeadStore = new HostedOptionKey<>("");

        @Option(help = "How the counts name this build. Empty: from the other options (graal, kills, objects or decisions).", stability = OptionStability.EXPERIMENTAL)//
        public static final HostedOptionKey<String> SideEffectAnalysisLabel = new HostedOptionKey<>("");
    }

    private final Path out = Path.of(Options.SideEffectAnalysisOutput.getValue());
    private final List<String> program = List.of(Options.SideEffectAnalysisProgram.getValue().split(","));
    private final boolean narrow = Options.SideEffectAnalysisNarrowCalls.getValue();
    private final String partition = Options.SideEffectAnalysisPartition.getValue();
    private final boolean decisions = Options.SideEffectAnalysisRemoveDeadStores.getValue();
    private final boolean overwrittenStores = Options.SideEffectAnalysisEliminateOverwrittenStores.getValue();
    private final boolean vm = Options.SideEffectAnalysisKillVMState.getValue();
    private final boolean platform = Options.SideEffectAnalysisKillPlatformFields.getValue();
    private final List<String> only = prefixes(Options.SideEffectAnalysisOnlyMethods.getValue());
    private final List<String> skip = prefixes(Options.SideEffectAnalysisSkipMethods.getValue());
    private final String label = !Options.SideEffectAnalysisLabel.getValue().isEmpty() ? Options.SideEffectAnalysisLabel.getValue()
                    : !narrow ? "graal" : decisions ? "decisions" : overwrittenStores ? "graal-dse" : partition.equals("field") ? "kills" : "objects";

    /** Method name and descriptor -> the partitions it may write; absent: anything. */
    private final Map<String, List<String>> written = new HashMap<>();
    /** Where an access is, a tab, and its field -> its partition. */
    private final Map<String, String> located = new HashMap<>();
    /** Where a store our rules find dead is, a tab, and its field. */
    private final Set<String> dead = new HashSet<>();
    /** The image's fields by name, to give Graal's locations for the partitions. */
    private final Map<String, HostedField> fields = new HashMap<>();
    /** The VM's state every narrowed call kills: see the class comment. */
    private final List<LocationIdentity> vmState = new ArrayList<>();
    /** What the low tier leaves of each of the program's methods, and the calls narrowed in it. */
    private final Map<String, String> counts = new ConcurrentHashMap<>();
    private final Map<String, List<String>> narrowed = new ConcurrentHashMap<>();

    @Override
    public boolean isInConfiguration(IsInConfigurationAccess access) {
        return Options.SideEffectAnalysis.getValue();
    }

    @Override
    public void afterAnalysis(AfterAnalysisAccess access) {
        if (!narrow) {
            return;
        }
        FeatureImpl.AfterAnalysisAccessImpl impl = (FeatureImpl.AfterAnalysisAccessImpl) access;
        Path export = out.resolve("export.json");
        Path answer = out.resolve("kills.txt");
        Path partitions = out.resolve("accesses.txt");
        try {
            Files.createDirectories(out);
            PointsToExport.export((PointsToAnalysis) impl.getBigBang(), impl.getUniverse(), "", export.toString(), null, true, "");
            List<String> command = new ArrayList<>(List.of(Options.SideEffectAnalysisUv.getValue(), "run", "--project", Options.SideEffectAnalysisTool.getValue(),
                            "python", "-m", "effects.kills", export.toString(), "-o", answer.toString(), "--partition", partition));
            if (!partition.equals("field")) {
                command.addAll(List.of("--accesses", partitions.toString()));
            }
            Process tool = new ProcessBuilder(command).inheritIO().start();
            if (tool.waitFor() != 0) {
                throw new IllegalStateException("effects.kills failed on " + export);
            }
            for (String line : Files.readAllLines(answer)) {
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
            if (decisions) {
                Path stores = out.resolve("dead.txt");
                Process rules = new ProcessBuilder(Options.SideEffectAnalysisUv.getValue(), "run", "--project", Options.SideEffectAnalysisTool.getValue(),
                                "python", "-m", "rules.decisions", export.toString(), "-o", stores.toString(), "--partition", partition).inheritIO().start();
                if (rules.waitFor() != 0) {
                    throw new IllegalStateException("rules.decisions failed on " + export);
                }
                dead.addAll(Files.readAllLines(stores));
            }
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

    @Override
    public void beforeCompilation(BeforeCompilationAccess access) {
        for (HostedField field : ((FeatureImpl.BeforeCompilationAccessImpl) access).getUniverse().getFields()) {
            fields.put(name(field), field);
        }
        // What Native Image's safepoint kills (SafepointSnippets), and initialization.
        vmState.addAll(List.of(com.oracle.svm.core.graal.snippets.SubstrateAllocationSnippets.GC_LOCATIONS));
        vmState.add(com.oracle.svm.core.thread.SafepointCheckCounter.getLocationIdentity());
        HostedField sessionState = fields.get("jdk.internal.foreign.MemorySessionImpl.state");
        if (sessionState != null) {
            vmState.add(new FieldLocationIdentity(sessionState));
        }
        vmState.add(LocationIdentity.init());
    }

    private static String name(jdk.vm.ci.meta.ResolvedJavaField field) {
        return field.getDeclaringClass().toJavaName(true) + "." + field.getName();
    }

    /**
     * Graal's locations for a partition the tool names: a field, an array kind, or with objects
     * told apart a field of a set of them, Aliasing$Counter.value@main:199. A field this graph
     * gives partitions is killed in its partition, and as a whole too, for the phases that key
     * field accesses by the field alone, such as read elimination; any other is killed whole.
     */
    private List<LocationIdentity> locations(String written, Set<String> partitioned) {
        if (written.equals("init")) {
            return vm ? List.of(LocationIdentity.init()) : List.of();
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
        if (field == null || (!platform && !PointsToExport.isProgramClass(field.getDeclaringClass().toJavaName(true)))) {
            return List.of(); // the image never accesses it, so there is nothing to kill; or the control
        }
        return partitioned.contains(whole) ? List.of(new FieldLocationIdentity(field), new FieldLocationIdentity(field, false, written))
                        : List.of(new FieldLocationIdentity(field));
    }

    /** The element kinds of an export's array partition: byte[] stands for boolean[] too. */
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
            default -> throw new IllegalArgumentException("not an array kind: " + name);
        };
    }

    @Override
    public void registerGraalPhases(Providers providers, Suites suites, boolean hosted, boolean fallback) {
        if (hosted) {
            if (narrow) {
                /*
                 * After Native Image's inliners, where it puts RemoveUnwindPhase, so that the calls
                 * and stores that inlining brings into a method get the analysis too. Before them
                 * only canonicalization runs, which no kill set changes.
                 */
                ListIterator<BasePhase<? super HighTierContext>> afterInlining = suites.getHighTier().findPhase(RemoveUnwindPhase.class);
                if (afterInlining != null) {
                    afterInlining.add(new ApplySideEffectAnalysisPhase());
                    if (overwrittenStores) {
                        afterInlining.add(new EliminateOverwrittenStoresPhase());
                    }
                } else {
                    if (overwrittenStores) {
                        suites.getHighTier().prependPhase(new EliminateOverwrittenStoresPhase());
                    }
                    suites.getHighTier().prependPhase(new ApplySideEffectAnalysisPhase());
                }
            }
            if (!partition.equals("field")) {
                suites.getMidTier().prependPhase(new VerifyFieldPartitionsPhase());
            }
            suites.getLowTier().appendPhase(new CountFieldAccessesPhase());
        }
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
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private boolean inProgram(ResolvedJavaMethod method) {
        String holder = method.getDeclaringClass().toJavaName(true);
        if (program.stream().allMatch(String::isEmpty)) {
            return PointsToExport.isProgramClass(holder);
        }
        return program.stream().anyMatch(prefix -> !prefix.isEmpty() && holder.startsWith(prefix));
    }

    private static List<String> prefixes(String commaSeparated) {
        return java.util.Arrays.stream(commaSeparated.split(",")).filter(prefix -> !prefix.isEmpty()).toList();
    }

    /** Whether the calls in a method are narrowed: the only and skip options limit it. */
    private boolean narrowsIn(ResolvedJavaMethod method) {
        String name = key(method);
        return (only.isEmpty() || only.stream().anyMatch(name::startsWith)) && skip.stream().noneMatch(name::startsWith);
    }

    /** As the exporter names a method: Examples.length(LExamples$Link;)I. */
    private static String key(ResolvedJavaMethod method) {
        return method.getDeclaringClass().toJavaName(true) + "." + method.getName() + method.getSignature().toMethodDescriptor();
    }

    /** As graal-probe names a method: Examples.length(Link). */
    private static String probeName(ResolvedJavaMethod method) {
        String parameters = java.util.stream.IntStream.range(0, method.getSignature().getParameterCount(false))
                        .mapToObj(i -> simple(method.getSignature().getParameterType(i, null).toJavaName(true)))
                        .collect(Collectors.joining(", "));
        return method.getDeclaringClass().toJavaName(false) + "." + method.getName() + "(" + parameters + ")";
    }

    private static String simple(String name) {
        return name.substring(Math.max(name.lastIndexOf('.'), name.lastIndexOf('$')) + 1);
    }

    /** What a call may write: the kills of every method it may call, null for anything. */
    private LocationIdentity[] killsOf(MethodCallTargetNode target, Set<String> partitioned) {
        HostedMethod method = (HostedMethod) target.targetMethod();
        HostedMethod[] callees = target.invokeKind().isDireict() ? new HostedMethod[]{method} : method.getImplementations();
        if (callees.length == 0) {
            return null;
        }
        List<LocationIdentity> all = new ArrayList<>();
        for (HostedMethod callee : callees) {
            List<String> partitions = written.get(key(callee));
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
     * in every copy of it: a store dead in it is overwritten, on every path inside it, before it
     * returns or throws, and an access's partition covers every context it is reached in.
     */
    private static List<String> sitesOf(String position) {
        List<String> sites = new ArrayList<>();
        String site = position;
        while (true) {
            sites.add(site);
            int outermost = site.lastIndexOf(" in ");
            if (outermost < 0) {
                return sites;
            }
            site = site.substring(0, outermost);
        }
    }

    /**
     * Removes the stores the tool's rules find dead, and the ones the control claims are, also in
     * the copies inlining made of them.
     */
    private void removeDeadStores(StructuredGraph graph, List<String> report) {
        String claimed = Options.SideEffectAnalysisClaimDeadStore.getValue();
        if (dead.isEmpty() && claimed.isEmpty()) {
            return;
        }
        for (StoreFieldNode store : graph.getNodes().filter(StoreFieldNode.class).snapshot()) {
            String at = PointsToExport.position(store.getNodeSourcePosition());
            String field = name(store.field());
            if (at != null && sitesOf(at).stream().anyMatch(site -> dead.contains(site + "\t" + field) || site.equals(claimed))) {
                jdk.graal.compiler.nodes.util.GraphUtil.removeFixedWithUnusedInputs(store);
                report.add(String.format("dead store to %s at bci %d removed", simple(name(store.field()).substring(0, name(store.field()).lastIndexOf('.')))
                                + name(store.field()).substring(name(store.field()).lastIndexOf('.')), store.getNodeSourcePosition().getBCI()));
            }
        }
    }

    /** The reference an access goes through, for the split: a parameter, or any other value. */
    @SuppressWarnings("deprecation") // a node's id, only to tell values of this graph apart
    private static String reference(AccessFieldNode access) {
        return jdk.graal.compiler.nodes.util.GraphUtil.unproxify(access.object()) instanceof jdk.graal.compiler.nodes.ParameterNode parameter
                        ? "param" + parameter.index() : "v" + access.object().getId();
    }

    /**
     * Gives each access to a field the location of its partition, if every access to the field in
     * the graph has one and they aren't all of one partition; the others keep the field's. An
     * access inlining copied takes the partition of the most specific site it is named by. Returns
     * the fields given partitions.
     */
    private Set<String> partition(StructuredGraph graph, List<String> report) {
        boolean split = key(graph.method()).equals(Options.SideEffectAnalysisClaimNoAliasing.getValue());
        Map<String, List<AccessFieldNode>> byField = new TreeMap<>();
        for (AccessFieldNode access : graph.getNodes().filter(AccessFieldNode.class)) {
            byField.computeIfAbsent(name(access.field()), k -> new ArrayList<>()).add(access);
        }
        Set<String> partitioned = new HashSet<>();
        for (Map.Entry<String, List<AccessFieldNode>> field : byField.entrySet()) {
            List<String> partitions = new ArrayList<>();
            for (AccessFieldNode access : field.getValue()) {
                String at = PointsToExport.position(access.getNodeSourcePosition());
                String found = at == null || access.getLocationIdentity().isImmutable() || access.ordersMemoryAccesses() ? null
                                : sitesOf(at).stream().map(site -> located.get(site + "\t" + field.getKey())).filter(java.util.Objects::nonNull).findFirst().orElse(null);
                partitions.add(found == null || !split ? found : found + "#" + reference(access));
            }
            if (partitions.contains(null) || partitions.stream().allMatch(field.getKey()::equals)) {
                continue;
            }
            for (int i = 0; i < partitions.size(); i++) {
                field.getValue().get(i).setLocationIdentity(new FieldLocationIdentity(field.getValue().get(i).field(), false, partitions.get(i)));
            }
            partitioned.add(field.getKey());
            report.add(String.format("%s in %s", simple(field.getKey().substring(0, field.getKey().lastIndexOf('.'))) + field.getKey().substring(field.getKey().lastIndexOf('.')),
                            new java.util.TreeSet<>(partitions).stream().map(p -> p.contains("@") ? p.substring(p.indexOf('@')) : p).collect(Collectors.joining(" "))));
        }
        return partitioned;
    }

    /**
     * Applies the analysis to one of the program's methods, right after Native Image's inliners:
     * removes the stores found dead, gives accesses their partitions, and narrows each call, and the
     * entry of its exception handler, to what its callees may write. Inlined code included: a call's kill set belongs to its targets, not
     * to where the call is.
     */
    private final class ApplySideEffectAnalysisPhase extends Phase {
        @Override
        public Optional<NotApplicable> notApplicableTo(GraphState graphState) {
            return ALWAYS_APPLICABLE;
        }

        @Override
        protected void run(StructuredGraph graph) {
            if (!inProgram(graph.method())) {
                return;
            }
            List<String> calls = new ArrayList<>();
            removeDeadStores(graph, calls);
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
                            // The handler is entered after the callee threw: before it did, it may have written what it writes otherwise.
                            handler.setKilledLocationIdentities(killed.toArray(new LocationIdentity[0]));
                        }
                        LocationIdentity[] set = Invoke.killSet(java.util.Arrays.stream(locations).filter(l -> !l.isInit() && !vmState.contains(l)).toArray(LocationIdentity[]::new));
                        calls.add(String.format("%s kills %s", probeName(target.targetMethod()), set.length == 0 ? "nothing"
                                        : java.util.Arrays.stream(set).map(l -> simple(l.toString())).collect(Collectors.joining(" "))));
                    }
                }
            }
            if (!calls.isEmpty()) {
                Collections.sort(calls);
                narrowed.put(probeName(graph.method()), calls);
            }
            graph.getDebug().dump(DebugContext.BASIC_LEVEL, graph, "After applying the side-effect analysis");
        }
    }

    /**
     * Runs Graal's {@link OverwrittenStoreEliminationPhase} on one of the program's methods, after
     * the analysis is applied (so with its partitions), and reports each store it removes.
     */
    private final class EliminateOverwrittenStoresPhase extends Phase {
        @Override
        public Optional<NotApplicable> notApplicableTo(GraphState graphState) {
            return ALWAYS_APPLICABLE;
        }

        @Override
        protected void run(StructuredGraph graph) {
            if (!inProgram(graph.method())) {
                return;
            }
            List<String> removed = new ArrayList<>();
            for (StoreFieldNode store : OverwrittenStoreEliminationPhase.overwrittenStores(graph)) {
                String field = name(store.field());
                removed.add(String.format("overwritten store to %s at bci %d removed", simple(field.substring(0, field.lastIndexOf('.'))) + field.substring(field.lastIndexOf('.')),
                                store.getNodeSourcePosition() != null ? store.getNodeSourcePosition().getBCI() : -1));
                jdk.graal.compiler.nodes.util.GraphUtil.removeFixedWithUnusedInputs(store);
            }
            if (!removed.isEmpty()) {
                narrowed.merge(probeName(graph.method()), removed, (calls, more) -> {
                    List<String> all = new ArrayList<>(calls);
                    all.addAll(more);
                    Collections.sort(all);
                    return all;
                });
            }
            graph.getDebug().dump(DebugContext.BASIC_LEVEL, graph, "After eliminating overwritten stores");
        }
    }

    /**
     * Stops the build if a graph has accesses to one field both with and without a partition, as
     * a phase that makes a new access after the partitioning could: their locations would not
     * overlap, and nothing would order them.
     */
    private final class VerifyFieldPartitionsPhase extends Phase {
        @Override
        public Optional<NotApplicable> notApplicableTo(GraphState graphState) {
            return ALWAYS_APPLICABLE;
        }

        @Override
        protected void run(StructuredGraph graph) {
            Map<jdk.vm.ci.meta.ResolvedJavaField, Set<Boolean>> kinds = new HashMap<>();
            for (Node node : graph.getNodes()) {
                if (node instanceof MemoryAccess access && access.getLocationIdentity() instanceof FieldLocationIdentity field && !field.isImmutable()) {
                    kinds.computeIfAbsent(field.getField(), k -> new HashSet<>()).add(field.getPartition() != null);
                }
            }
            kinds.forEach((field, partitioned) -> {
                if (partitioned.size() > 1) {
                    throw new IllegalStateException(graph.method().format("%H.%n") + " accesses " + name(field) + " both with and without a partition");
                }
            });
        }
    }

    private final class CountFieldAccessesPhase extends Phase {
        @Override
        public Optional<NotApplicable> notApplicableTo(GraphState graphState) {
            return ALWAYS_APPLICABLE;
        }

        @Override
        protected void run(StructuredGraph graph) {
            if (!inProgram(graph.method())) {
                return;
            }
            ControlFlowGraph cfg = ControlFlowGraph.newBuilder(graph).connectBlocks(true).computeLoops(true).build();
            Map<String, Integer> writes = new TreeMap<>();
            Map<String, Integer> reads = new TreeMap<>();
            int calls = 0;
            for (Node node : graph.getNodes()) {
                if (node instanceof Invoke) {
                    calls++;
                } else if (node instanceof MemoryAccess access && access.getLocationIdentity() instanceof FieldLocationIdentity field) {
                    HIRBlock block = cfg.blockFor(node);
                    boolean loop = block != null && block.getLoop() != null;
                    String where = simple(field.getField().format("%H")) + "." + field.getField().getName() + (loop ? "(loop)" : "");
                    Map<String, Integer> counted = node instanceof StoreFieldNode || node instanceof AbstractWriteNode ? writes
                                    : node instanceof LoadFieldNode || node instanceof ReadNode || node instanceof FloatingReadNode ? reads : null;
                    if (counted != null) {
                        counted.merge(where, 1, Integer::sum);
                    }
                }
            }
            counts.put(probeName(graph.method()), String.format("calls %d   writes %-32s reads %s", calls, show(writes), show(reads)));
        }

        private static String show(Map<String, Integer> counted) {
            return counted.isEmpty() ? "-"
                            : counted.entrySet().stream().map(e -> e.getKey() + (e.getValue() > 1 ? "×" + e.getValue() : "")).collect(Collectors.joining(" "));
        }
    }
}
