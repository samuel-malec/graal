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
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.graph.NodeSourcePosition;
import jdk.graal.compiler.nodes.AbstractDeoptimizeNode;
import jdk.graal.compiler.nodes.ControlSplitNode;
import jdk.graal.compiler.nodes.FieldLocationIdentity;
import jdk.graal.compiler.nodes.FixedNode;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.InvokeWithExceptionNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.cfg.ControlFlowGraph;
import jdk.graal.compiler.nodes.cfg.HIRBlock;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.memory.AbstractWriteNode;
import jdk.graal.compiler.nodes.memory.FloatingReadNode;
import jdk.graal.compiler.nodes.memory.MemoryAccess;
import jdk.graal.compiler.nodes.memory.ReadNode;

/**
 * Measurement only: records what reaches the end of the low tier in each of the program's
 * methods. Writes counts.txt (calls, field loads and stores left; calls narrowed, fields
 * partitioned, locks and stores removed), control.txt (control flow), sites.txt (where each
 * access is), shape.txt (graph size and paths) and inlined.txt (the inlining it was built from).
 */
final class CompiledCodeCounts {
    /** The address at the end of a hidden class's name changes between builds; the content hash before it doesn't. */
    private static final Pattern HIDDEN_CLASS_ADDRESS = Pattern.compile("/0x[0-9a-f]+");

    private final String program;
    /** Per method: the counts, plus what the phases changed (calls narrowed, fields partitioned, locks and stores removed). */
    private final Map<String, String> counts = new ConcurrentHashMap<>();
    private final Map<String, List<String>> changes = new ConcurrentHashMap<>();
    /** Per method: control flow (control.txt), and the position of each field access left, with its inlining and whether it is in a loop (sites.txt). */
    private final Map<String, String> control = new ConcurrentHashMap<>();
    private final Map<String, List<String>> sites = new ConcurrentHashMap<>();
    /** Per method: the graph's shape apart from loads and stores, for comparing builds despite inlining and unrolling (shape.txt). */
    private final Map<String, String> shape = new ConcurrentHashMap<>();
    /** Per method: the call sites inlined into it, as {@code callee < caller@bci < ...} (inlined.txt), to tell a removed load from one never inlined. */
    private final Map<String, TreeSet<String>> inlinedSites = new ConcurrentHashMap<>();

    CompiledCodeCounts(String program) {
        this.program = program;
    }

    /** Creates the phase that records the counts. */
    TimedPhase newPhase(StepTimes times) {
        return new CountPhase(times);
    }

    /** Replaces what is listed for a method with the changes a phase made (partitions given, calls narrowed), sorted. */
    void listChanges(StructuredGraph graph, List<String> sorted) {
        changes.put(Names.readableName(graph.method()), sorted);
    }

    /** Adds a phase's changes to what is listed for a method, keeping it sorted. */
    void addChanges(StructuredGraph graph, List<String> more) {
        changes.merge(Names.readableName(graph.method()), more, (before, added) -> {
            List<String> all = new ArrayList<>(before);
            all.addAll(added);
            Collections.sort(all);
            return all;
        });
    }

    /** Writes counts.txt (each method's counts under {@code label}, the build's name, plus the changes), control.txt, shape.txt, inlined.txt and sites.txt. */
    void write(Path out, String label) throws IOException {
        StringBuilder text = new StringBuilder();
        for (Map.Entry<String, String> method : new TreeMap<>(counts).entrySet()) {
            text.append(method.getKey()).append('\n').append(String.format("    %-10s %s%n", label, method.getValue()));
            for (String change : changes.getOrDefault(method.getKey(), List.of())) {
                text.append("        ").append(change).append('\n');
            }
        }
        Files.writeString(out.resolve("counts.txt"), text);
        writeRows(out.resolve("control.txt"), "# method\tblocks\tcontrol-flow edges\tifs\tswitches and other splits\tloops\tcalls with an exception edge\tdeoptimizations\n", control);
        writeRows(out.resolve("shape.txt"), "# method\tnodes\tfixed nodes\tlongest path in blocks (back edges cut)\tlongest path in fixed nodes\tdeepest loop\tinlined call sites" +
                        "\tinlining hash (0 without -H:+TrackNodeSourcePosition)\tif places (each if once, however many copies unrolling made)\tcall places\tifs without a place\n", shape);
        writeLines(out.resolve("inlined.txt"), "# method\tinlined call site: callee < caller@bci < ... (the callee is the method that was inlined; empty without -H:+TrackNodeSourcePosition)\n",
                        inlinedSites);
        writeLines(out.resolve("sites.txt"), "# method\tload or store\tin a loop or not\tfield\tinlining it came through, innermost first (- without -H:+TrackNodeSourcePosition)\n", sites);
    }

    /** Writes one row per method, sorted by name, under a header. */
    private static void writeRows(Path file, String header, Map<String, String> rows) throws IOException {
        StringBuilder text = new StringBuilder(header);
        new TreeMap<>(rows).forEach((method, row) -> text.append(method).append('\t').append(row).append('\n'));
        Files.writeString(file, text);
    }

    /** Writes any number of rows per method, sorted by name, under a header. */
    private static void writeLines(Path file, String header, Map<String, ? extends Collection<String>> lines) throws IOException {
        StringBuilder text = new StringBuilder(header);
        new TreeMap<>(lines).forEach((method, list) -> list.forEach(line -> text.append(method).append('\t').append(line).append('\n')));
        Files.writeString(file, text);
    }

    /** Records what the low tier leaves of one of the program's methods; changes nothing. */
    private final class CountPhase extends TimedPhase {
        CountPhase(StepTimes times) {
            super(times, "count accesses (measurement only)");
        }

        @Override
        protected void runOn(StructuredGraph graph) {
            if (!Names.inProgram(graph.method(), program)) {
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
                    countAccess(node, field, cfg, writes, reads, accessSites);
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
            String method = Names.readableName(graph.method());
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
    }

    /** Counts a field load or store, by field and whether it is in a loop, and records its position. Other accesses to the field's location are not counted. */
    private static void countAccess(Node node, FieldLocationIdentity field, ControlFlowGraph cfg, Map<String, Integer> writes, Map<String, Integer> reads, List<String> accessSites) {
        HIRBlock block = cfg.blockFor(node);
        boolean loop = block != null && block.getLoop() != null;
        String name = Names.simpleName(field.getField().format("%H")) + "." + field.getField().getName();
        boolean store = node instanceof StoreFieldNode || node instanceof AbstractWriteNode;
        Map<String, Integer> counted = store ? writes
                        : node instanceof LoadFieldNode || node instanceof ReadNode || node instanceof FloatingReadNode ? reads : null;
        if (counted != null) {
            counted.merge(name + (loop ? "(loop)" : ""), 1, Integer::sum);
            accessSites.add(String.join("\t", store ? "store" : "load", loop ? "loop" : "flat", name, position(node)));
        }
    }

    /** The call sites inlined into a graph, each once, as {@code callee < caller@bci < ...}: every frame of a node's position except the outermost. */
    private static TreeSet<String> inlinedCallSites(StructuredGraph graph) {
        TreeSet<String> inlined = new TreeSet<>();
        for (Node node : graph.getNodes()) {
            NodeSourcePosition position = node.getNodeSourcePosition();
            if (position == null) {
                continue;
            }
            for (NodeSourcePosition frame = position; frame.getCaller() != null; frame = frame.getCaller()) {
                StringBuilder callSite = new StringBuilder(Names.readableName(frame.getMethod()));
                for (NodeSourcePosition caller = frame.getCaller(); caller != null; caller = caller.getCaller()) {
                    callSite.append(" < ").append(Names.readableName(caller.getMethod())).append('@').append(caller.getBCI());
                }
                inlined.add(HIDDEN_CLASS_ADDRESS.matcher(callSite).replaceAll("/0xH"));
            }
        }
        return inlined;
    }

    /**
     * The graph's shape: nodes and fixed nodes, the longest path with back edges cut (in blocks and
     * in fixed nodes), the deepest loop nesting, and the inlining (number of distinct inlined call
     * sites and a hash of them, so methods with different inlining can be told apart; 0 and 0
     * without -H:+TrackNodeSourcePosition).
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
                if (successor > i) { // forward edges only: loop back edges are cut
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
        return String.join("\t", Integer.toString(graph.getNodeCount()), Integer.toString(fixedNodes), Integer.toString(longestInBlocks), Integer.toString(longestInFixedNodes),
                        Integer.toString(deepestLoop), Integer.toString(inlined.size()), inliningHash(inlined), Integer.toString(ifPlaces.size()), Integer.toString(callPlaces.size()),
                        Integer.toString(ifsWithoutPlace));
    }

    /** The first 8 hex digits of the SHA-256 of the inlined call sites (one per line); 0 for none. */
    private static String inliningHash(TreeSet<String> inlined) {
        if (inlined.isEmpty()) {
            return "0";
        }
        try {
            byte[] digest = MessageDigest.getInstance("SHA-256").digest(String.join("\n", inlined).getBytes(StandardCharsets.UTF_8));
            return String.format("%02x%02x%02x%02x", digest[0], digest[1], digest[2], digest[3]);
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException(e);
        }
    }

    /**
     * The inlining a node came through, innermost first, as {@code method@bci}: the same access
     * inlined at two call sites counts as two places. {@code -} without source positions
     * (-H:+TrackNodeSourcePosition).
     */
    private static String position(Node node) {
        NodeSourcePosition position = node.getNodeSourcePosition();
        if (position == null) {
            return "-";
        }
        StringBuilder chain = new StringBuilder();
        for (NodeSourcePosition at = position; at != null; at = at.getCaller()) {
            chain.append(chain.length() == 0 ? "" : " < ").append(Names.readableName(at.getMethod())).append('@').append(at.getBCI());
        }
        return chain.toString();
    }

    /** Counted accesses for counts.txt: each field, with a count if more than one; {@code -} for none. */
    private static String show(Map<String, Integer> counted) {
        return counted.isEmpty() ? "-"
                        : counted.entrySet().stream().map(e -> e.getKey() + (e.getValue() > 1 ? "\u00d7" + e.getValue() : "")).collect(Collectors.joining(" "));
    }
}
