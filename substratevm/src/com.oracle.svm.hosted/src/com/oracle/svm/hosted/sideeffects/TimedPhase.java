package com.oracle.svm.hosted.sideeffects;

import java.util.Optional;

import jdk.graal.compiler.nodes.GraphState;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.phases.Phase;

/**
 * A phase of the side-effect analysis: it applies to every graph, and the time it takes is added
 * to its step in timings.txt.
 */
abstract class TimedPhase extends Phase {
    private final StepTimes times;
    private final String step;

    TimedPhase(StepTimes times, String step) {
        this.times = times;
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
            times.time(step, start);
        }
    }

    protected abstract void runOn(StructuredGraph graph);
}
