package com.oracle.svm.hosted.sideeffects;

import java.util.Locale;
import java.util.Map;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.LongAdder;

/**
 * What each step of the analysis cost in this build, in nanoseconds, and how often it ran: the
 * export and the tool once, each phase once per graph, summed over the compiler's threads. Written
 * to timings.txt, with the size of the export.
 */
final class StepTimes {
    private final Map<String, LongAdder> nanos = new ConcurrentHashMap<>();
    private final Map<String, LongAdder> runs = new ConcurrentHashMap<>();

    /**
     * Adds the time since {@code start} to a step of the analysis.
     */
    void time(String step, long start) {
        add(step, System.nanoTime() - start);
    }

    /**
     * Adds one run of a step that took this long.
     */
    void add(String step, long stepNanos) {
        nanos.computeIfAbsent(step, k -> new LongAdder()).add(stepNanos);
        runs.computeIfAbsent(step, k -> new LongAdder()).increment();
    }

    /**
     * Appends a line for each step, in the order of their names: the step, its seconds, its runs.
     */
    void appendTo(StringBuilder timings) {
        for (Map.Entry<String, LongAdder> step : new TreeMap<>(nanos).entrySet()) {
            timings.append(String.format(Locale.ROOT, "%s\t%.3f\t%d%n", step.getKey(), step.getValue().sum() / 1e9, runs.get(step.getKey()).sum()));
        }
    }
}
