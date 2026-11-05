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
