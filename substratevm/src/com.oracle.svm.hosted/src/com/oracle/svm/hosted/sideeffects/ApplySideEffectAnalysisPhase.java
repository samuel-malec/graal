package com.oracle.svm.hosted.sideeffects;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.graalvm.word.LocationIdentity;

import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.InvokeWithExceptionNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.java.ExceptionObjectNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Applies the analysis to one of the program's methods, right after Native Image's inliners:
 * gives accesses their partitions, and narrows each call, and the entry of its exception handler,
 * to what its callees may write. Inlined code included: a call's kill set belongs to its targets,
 * not to where the call is.
 */
final class ApplySideEffectAnalysisPhase extends TimedPhase {
    private final KillSets killSets;
    private final FieldPartitions partitions;
    private final String program;
    private final List<String> only;
    private final List<String> skip;
    private final CompiledCodeCounts counts;

    /**
     * @param only the methods whose calls are narrowed, by prefix: all if none
     * @param skip the methods whose calls are not
     */
    ApplySideEffectAnalysisPhase(StepTimes times, KillSets killSets, FieldPartitions partitions, String program, List<String> only, List<String> skip, CompiledCodeCounts counts) {
        super(times, "apply");
        this.killSets = killSets;
        this.partitions = partitions;
        this.program = program;
        this.only = only;
        this.skip = skip;
        this.counts = counts;
    }

    @Override
    protected void runOn(StructuredGraph graph) {
        if (!Names.inProgram(graph.method(), program)) {
            return;
        }
        List<String> calls = new ArrayList<>();
        Set<String> partitioned = partitions.isEmpty() ? Set.of() : partitions.partition(graph, calls);
        boolean narrows = narrowsIn(graph.method());
        for (Node node : graph.getNodes()) {
            if (narrows && node instanceof Invoke invoke && invoke.callTarget() instanceof MethodCallTargetNode target) {
                LocationIdentity[] locations = killSets.killsOf(target, partitioned);
                if (locations != null) {
                    List<LocationIdentity> killed = new ArrayList<>(List.of(locations));
                    killed.addAll(killSets.killedByEveryCall());
                    invoke.setKilledLocationIdentities(killed.toArray(new LocationIdentity[0]));
                    if (invoke instanceof InvokeWithExceptionNode withException && withException.exceptionEdge() instanceof ExceptionObjectNode handler) {
                        // The handler is entered after the callee threw: before it did, it may
                        // have written what it writes otherwise.
                        handler.setKilledLocationIdentities(killed.toArray(new LocationIdentity[0]));
                    }
                    LocationIdentity[] set = Invoke.killSet(Arrays.stream(locations).filter(l -> !killSets.isVMState(l)).toArray(LocationIdentity[]::new));
                    calls.add(String.format("%s kills %s", Names.readableName(target.targetMethod()), set.length == 0 ? "nothing"
                                    : Arrays.stream(set).map(l -> Names.simpleName(l.toString())).collect(Collectors.joining(" "))));
                }
            }
        }
        if (!calls.isEmpty()) {
            Collections.sort(calls);
            counts.listChanges(graph, calls);
        }
        graph.getDebug().dump(DebugContext.BASIC_LEVEL, graph, "After applying the side-effect analysis");
    }

    /**
     * Whether the calls in a method are narrowed: the only and skip options limit it.
     */
    private boolean narrowsIn(ResolvedJavaMethod method) {
        String name = Names.exportName(method);
        return (only.isEmpty() || only.stream().anyMatch(name::startsWith)) && skip.stream().noneMatch(name::startsWith);
    }
}
