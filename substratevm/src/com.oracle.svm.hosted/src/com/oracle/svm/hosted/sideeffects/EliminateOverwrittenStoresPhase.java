package com.oracle.svm.hosted.sideeffects;

import java.util.ArrayList;
import java.util.List;

import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.util.GraphUtil;
import jdk.graal.compiler.phases.common.OverwrittenStoreEliminationPhase;

/**
 * Runs Graal's {@link OverwrittenStoreEliminationPhase} on one of the program's methods, after the
 * analysis is applied (so with its partitions), and reports each store it removes.
 */
final class EliminateOverwrittenStoresPhase extends TimedPhase {
    private final String program;
    private final CompiledCodeCounts counts;

    EliminateOverwrittenStoresPhase(StepTimes times, String program, CompiledCodeCounts counts) {
        super(times, "eliminate overwritten stores");
        this.program = program;
        this.counts = counts;
    }

    @Override
    protected void runOn(StructuredGraph graph) {
        if (!Names.inProgram(graph.method(), program)) {
            return;
        }
        List<String> removed = new ArrayList<>();
        for (StoreFieldNode store : OverwrittenStoreEliminationPhase.overwrittenStores(graph)) {
            removed.add(String.format("overwritten store to %s at bci %d removed", Names.shortField(Names.fieldName(store.field())),
                            store.getNodeSourcePosition() != null ? store.getNodeSourcePosition().getBCI() : -1));
            GraphUtil.removeFixedWithUnusedInputs(store);
        }
        if (!removed.isEmpty()) {
            counts.addChanges(graph, removed);
        }
        graph.getDebug().dump(DebugContext.BASIC_LEVEL, graph, "After eliminating overwritten stores");
    }
}
