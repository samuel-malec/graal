package com.oracle.svm.hosted.sideeffects;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.FieldLocationIdentity;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.memory.MemoryAccess;
import jdk.vm.ci.meta.ResolvedJavaField;

/**
 * Stops the build if a graph has accesses to one field both with and without a partition, as a
 * phase that makes a new access after the partitioning could: their locations would not overlap,
 * and nothing would order them.
 */
final class VerifyFieldPartitionsPhase extends TimedPhase {
    VerifyFieldPartitionsPhase(StepTimes times) {
        super(times, "verify partitions");
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
                throw new IllegalStateException(graph.method().format("%H.%n") + " accesses " + Names.fieldName(field) + " both with and without a partition");
            }
        });
    }
}
