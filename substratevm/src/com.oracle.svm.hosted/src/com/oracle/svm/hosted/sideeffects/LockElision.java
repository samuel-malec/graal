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
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import com.oracle.graal.pointsto.export.PointsToExport;
import com.oracle.svm.core.deopt.DeoptimizationSupport;

import jdk.graal.compiler.core.common.memory.MemoryOrderMode;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.extended.OSRMonitorEnterNode;
import jdk.graal.compiler.nodes.java.AccessFieldNode;
import jdk.graal.compiler.nodes.java.AccessMonitorNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.MonitorEnterNode;
import jdk.graal.compiler.nodes.java.MonitorExitNode;
import jdk.graal.compiler.nodes.java.MonitorIdNode;
import jdk.graal.compiler.nodes.util.GraphUtil;

/** Removes locks and makes volatile accesses plain on objects only one thread can reach, as the tool decides (effects.elide, locks.txt), and counts what was removed. */
final class LockElision {
    /** Position of a removable lock to enter/exit; position of a volatile access that can be plain to plain-read/plain-write, a tab, and its field. */
    private final Map<String, String> decisions = new HashMap<>();
    /** Test only: a method (as the export names it) whose locks and volatile accesses are claimed to be thread-local. */
    private final String claimedLocal;
    /** Test only: remove locks even in an image that can deoptimize. */
    private final boolean claimNoDeoptimization;
    // What was removed, summed over the compiler threads, for timings.txt.
    private final AtomicInteger monitorsRemoved = new AtomicInteger();
    private final AtomicInteger locksRemoved = new AtomicInteger();
    private final AtomicInteger locksKeptForDeoptimization = new AtomicInteger();
    private final AtomicInteger volatilesMadePlain = new AtomicInteger();

    LockElision(String claimedLocal, boolean claimNoDeoptimization) {
        this.claimedLocal = claimedLocal;
        this.claimNoDeoptimization = claimNoDeoptimization;
    }

    /** Reads the tool's decisions: per line a position, a tab, and the decision. */
    void read(Path locks) throws IOException {
        for (String line : Files.readAllLines(locks)) {
            String[] parts = line.split("\t", 2);
            decisions.put(parts[0], parts[1]);
        }
    }

    /** Appends to timings.txt how many locks and volatile accesses were removed, of how many listed. */
    void appendTo(StringBuilder timings) {
        timings.append(String.format("# locks removed: %d, with %d monitor enters and exits; volatile accesses made ordinary: %d; of %d sites the tool listed%n", locksRemoved.get(),
                        monitorsRemoved.get(), volatilesMadePlain.get(), decisions.size()));
        timings.append(String.format("# locks kept because the image can deoptimize: %d%n", locksKeptForDeoptimization.get()));
    }

    /** Creates the phase that removes locks and makes volatile accesses plain. */
    TimedPhase newPhase(StepTimes times, CompiledCodeCounts counts) {
        return new ElideLocksPhase(times, counts);
    }

    /** Whether the tool lists a node at {@code at} with this decision, or the test claim covers its method. */
    private boolean listedOrClaimed(String at, String decision) {
        return Names.sitesOf(at).stream().anyMatch(site -> decision.equals(decisions.get(site)) || !claimedLocal.isEmpty() && site.startsWith(claimedLocal + ":"));
    }

    /**
     * Removes the lock enters and exits that the tool lists, in every method, inlined code included.
     * A lock is removed entirely or not at all: its enter and every exit (including those on
     * exception paths) must be listed, or the frame states and remaining monitors would not match.
     * Positions need -H:+TrackNodeSourcePosition.
     * <p>
     * An image that can deoptimize keeps its locks. Code compiled at run time doesn't go through this
     * phase and takes the locks. If it deoptimizes inside a locked region, execution continues in the
     * image's version of the method, which must release that lock; without its monitors it wouldn't,
     * and the thread would hold the lock forever. Volatile accesses are not affected.
     */
    private final class ElideLocksPhase extends TimedPhase {
        private final CompiledCodeCounts counts;

        ElideLocksPhase(StepTimes times, CompiledCodeCounts counts) {
            super(times, "elide locks");
            this.counts = counts;
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
            boolean deoptimizes = DeoptimizationSupport.enabled() && !claimNoDeoptimization;
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
                counts.addChanges(graph, removed);
                graph.getDebug().dump(DebugContext.BASIC_LEVEL, graph, "After eliminating locks");
            }
        }

        /** Makes listed volatile accesses plain: on an object only one thread can reach, they synchronize with nothing. */
        private void makeVolatilesPlain(StructuredGraph graph, List<String> report) {
            for (AccessFieldNode access : graph.getNodes().filter(AccessFieldNode.class).snapshot()) {
                if (access.getMemoryOrder() != MemoryOrderMode.VOLATILE) {
                    continue;
                }
                String at = PointsToExport.position(access.getNodeSourcePosition());
                if (at == null) {
                    continue;
                }
                if (listedOrClaimed(at, (access instanceof LoadFieldNode ? "plain-read" : "plain-write") + "\t" + Names.fieldName(access.field()))) {
                    access.makePlain();
                    volatilesMadePlain.incrementAndGet();
                    report.add(String.format("volatile %s of %s at bci %d made ordinary", access instanceof LoadFieldNode ? "read" : "write", Names.shortField(Names.fieldName(access.field())),
                                    access.getNodeSourcePosition().getBCI()));
                }
            }
        }

        /** Whether the tool lists a lock enter or exit, or the test claim covers it. */
        private boolean listed(AccessMonitorNode monitor) {
            String kind = monitor instanceof MonitorEnterNode && !(monitor instanceof OSRMonitorEnterNode) ? "enter" : monitor instanceof MonitorExitNode ? "exit" : null;
            String at = PointsToExport.position(monitor.getNodeSourcePosition());
            if (kind == null || at == null) {
                return false;
            }
            return listedOrClaimed(at, kind);
        }
    }
}
