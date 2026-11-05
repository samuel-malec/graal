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

/**
 * The monitors and volatile accesses on objects only one thread reaches, as the tool decides them
 * (effects.elide, locks.txt), and how many of them the image lost.
 */
final class LockElision {
    /**
     * Where a monitor the tool says can go is -> enter or exit; where a volatile access that can
     * be made ordinary is -> plain-read or plain-write, a tab, and its field.
     */
    private final Map<String, String> decisions = new HashMap<>();
    /**
     * Control: a method, as the export names it, whose monitors and volatile accesses are claimed
     * to be on objects only one thread reaches.
     */
    private final String claimedLocal;
    /**
     * Control: remove the monitors even in an image that can deoptimize.
     */
    private final boolean claimNoDeoptimization;
    private final AtomicInteger monitorsRemoved = new AtomicInteger();
    private final AtomicInteger locksRemoved = new AtomicInteger();
    private final AtomicInteger locksKeptForDeoptimization = new AtomicInteger();
    private final AtomicInteger volatilesMadePlain = new AtomicInteger();

    LockElision(String claimedLocal, boolean claimNoDeoptimization) {
        this.claimedLocal = claimedLocal;
        this.claimNoDeoptimization = claimNoDeoptimization;
    }

    /** Reads the tool's decisions: where a node is, a tab, and what to do with it. */
    void read(Path locks) throws IOException {
        for (String line : Files.readAllLines(locks)) {
            String[] parts = line.split("\t", 2);
            decisions.put(parts[0], parts[1]);
        }
    }

    /** Appends to timings.txt how many locks and volatile accesses the image lost, of how many listed. */
    void appendTo(StringBuilder timings) {
        timings.append(String.format("# locks removed: %d, with %d monitor enters and exits; volatile accesses made ordinary: %d; of %d sites the tool listed%n", locksRemoved.get(),
                        monitorsRemoved.get(), volatilesMadePlain.get(), decisions.size()));
        timings.append(String.format("# locks kept because the image can deoptimize: %d%n", locksKeptForDeoptimization.get()));
    }

    /** The phase that removes the monitors and makes the volatile accesses ordinary. */
    TimedPhase newPhase(StepTimes times, CompiledCodeCounts counts) {
        return new ElideLocksPhase(times, counts);
    }

    /**
     * Whether the tool lists a node at {@code at} with this decision, or the control claims every
     * monitor and volatile access of its method local.
     */
    private boolean listedOrClaimed(String at, String decision) {
        return Names.sitesOf(at).stream().anyMatch(site -> decision.equals(decisions.get(site)) || !claimedLocal.isEmpty() && site.startsWith(claimedLocal + ":"));
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
                if (listedOrClaimed(at, (access instanceof LoadFieldNode ? "plain-read" : "plain-write") + "\t" + Names.fieldName(access.field()))) {
                    access.makePlain();
                    volatilesMadePlain.incrementAndGet();
                    report.add(String.format("volatile %s of %s at bci %d made ordinary", access instanceof LoadFieldNode ? "read" : "write", Names.shortField(Names.fieldName(access.field())),
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
}
