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
package com.oracle.graal.pointsto.export;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * Computes each method's kill set: the memory that a call to the method may write, including
 * through everything it calls. This is the in-builder version of the Python tool's
 * {@code effects.kills} (per-field partitions only) and produces the same {@code kills.txt}
 * lines: the method, a tab, then {@code any} or a comma-separated list of what it writes (field
 * names, array kinds such as {@code int[]}, {@code init} if it allocates, and VM locations such as
 * {@code vm:TLAB.top}).
 * <p>
 * A method's kill set is {@code any} if it, or anything it may call:
 * <ul>
 * <li>has a memory effect the collected information can't name,</li>
 * <li>synchronizes in a way that may order this thread with another,</li>
 * <li>makes a call the points-to analysis could not resolve, or</li>
 * <li>calls a method with no collected information.</li>
 * </ul>
 * Otherwise its kill set is the union of its own writes and those of its callees.
 */
final class KillSetComputation {
    static final String ANY = "any";
    static final String INIT = "init";

    // Placeholder object names, the same as in the Python tool (signatures.py): an object the
    // analysis can't name, the "object" of an access whose reference is always null, and the
    // holder of a class's static fields.
    private static final String UNKNOWN_OBJECT = "?";
    private static final String NO_OBJECT = "null";
    private static final String STATICS = ".<statics>";

    private KillSetComputation() {
    }

    /**
     * Returns one {@code kills.txt} line per method, sorted by name. {@code shared} is the set of
     * objects another thread may reach, or null if thread escape did not run, in which case every
     * acquire and release counts as synchronization with another thread.
     */
    static List<String> lines(PointsToExport.Facts facts, Set<String> shared) {
        TreeSet<String> names = new TreeSet<>(facts.analysed);
        names.addAll(facts.callees.keySet());
        String[] methods = names.toArray(new String[0]);
        Map<String, Integer> method = positions(methods);

        // Numbered in name order, so a BitSet lists them in the same order as the Python tool.
        TreeSet<String> partitionNames = new TreeSet<>();
        for (String m : methods) {
            partitionNames.addAll(facts.writes.getOrDefault(m, new TreeSet<>()));
            partitionNames.addAll(facts.vmWrites.getOrDefault(m, new TreeSet<>()));
        }
        partitionNames.add(INIT);
        String[] partitions = partitionNames.toArray(new String[0]);
        Map<String, Integer> partition = positions(partitions);

        int[][] callees = new int[methods.length][];
        boolean[] blocked = new boolean[methods.length];
        BitSet[] written = new BitSet[methods.length];
        for (int m = 0; m < methods.length; m++) {
            String name = methods[m];
            TreeSet<String> called = facts.callees.getOrDefault(name, new TreeSet<>());
            callees[m] = withFacts(called, method);
            boolean callsWithoutFacts = callees[m].length < called.size();
            blocked[m] = blocks(facts, name, shared, callsWithoutFacts);
            written[m] = ownWrites(facts, name, partition);
        }

        boolean[] any = reaching(callees, blocked);
        closeOverCallees(callees, any, written);

        List<String> lines = new ArrayList<>(methods.length);
        for (int m = 0; m < methods.length; m++) {
            lines.add(line(methods[m], any[m], written[m], partitions));
        }
        return lines;
    }

    /** Each name's index in the array. */
    private static Map<String, Integer> positions(String[] names) {
        Map<String, Integer> position = new HashMap<>();
        for (int i = 0; i < names.length; i++) {
            position.put(names[i], i);
        }
        return position;
    }

    /** The indices of the callees that have collected information, in name order. */
    private static int[] withFacts(TreeSet<String> called, Map<String, Integer> method) {
        int[] ids = new int[called.size()];
        int known = 0;
        for (String callee : called) {
            Integer id = method.get(callee);
            if (id != null) {
                ids[known++] = id;
            }
        }
        return Arrays.copyOf(ids, known);
    }

    /**
     * Whether the method itself forces {@code any} (the same test as {@code effects.kills.blocks}):
     * an unknown memory effect, synchronization with another thread, an unresolved call, or a call
     * to a method without collected information.
     */
    private static boolean blocks(PointsToExport.Facts facts, String method, Set<String> shared, boolean callsWithoutFacts) {
        return !facts.unknown.getOrDefault(method, new TreeSet<>()).isEmpty() ||
                        orders(facts.acquires.get(method), facts.locks.get(method), shared) ||
                        orders(facts.releases.get(method), facts.locks.get(method), shared) ||
                        !facts.unresolved.getOrDefault(method, new TreeSet<>()).isEmpty() || callsWithoutFacts;
    }

    /** What the method itself writes, as partition indices. */
    private static BitSet ownWrites(PointsToExport.Facts facts, String method, Map<String, Integer> partition) {
        BitSet own = new BitSet(partition.size());
        for (String p : facts.writes.getOrDefault(method, new TreeSet<>())) {
            own.set(partition.get(p));
        }
        for (String p : facts.vmWrites.getOrDefault(method, new TreeSet<>())) {
            own.set(partition.get(p));
        }
        if (facts.allocates.contains(method)) {
            own.set(partition.get(INIT));
        }
        return own;
    }

    /** Formats one {@code kills.txt} line. */
    private static String line(String method, boolean any, BitSet written, String[] partitions) {
        StringBuilder line = new StringBuilder(method).append('\t');
        if (any) {
            line.append(ANY);
        } else {
            String separator = "";
            for (int p = written.nextSetBit(0); p >= 0; p = written.nextSetBit(p + 1)) {
                line.append(separator).append(partitions[p]);
                separator = ",";
            }
        }
        return line.toString();
    }

    /**
     * Whether any of these acquires or releases may synchronize with another thread: one on an
     * object another thread may reach, or one whose objects are unknown.
     */
    @SuppressWarnings("unchecked")
    private static boolean orders(TreeSet<String> sites, TreeMap<String, Object> locks, Set<String> shared) {
        if (sites == null) {
            return false;
        }
        for (String site : sites) {
            if (locks == null || !locks.containsKey(site)) {
                return true;
            }
            Object objects = locks.get(site);
            if (objects == null) {
                return true;
            }
            for (String object : (List<String>) objects) {
                if (!object.equals(NO_OBJECT) && isShared(object, shared)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Whether another thread may reach the object (as {@code shared_object} in the Python tool):
     * true for an unnamed object, for static fields, for an object thread escape found shared, and
     * for every object when thread escape did not run.
     */
    private static boolean isShared(String object, Set<String> shared) {
        return shared == null || object.equals(UNKNOWN_OBJECT) || object.endsWith(STATICS) || shared.contains(object);
    }

    /** Marks the blocked methods and every method that may reach one of them through calls. */
    private static boolean[] reaching(int[][] callees, boolean[] blocked) {
        int[][] callers = callersOf(callees);
        boolean[] found = blocked.clone();
        int[] work = new int[callees.length];
        int size = 0;
        for (int m = 0; m < callees.length; m++) {
            if (found[m]) {
                work[size++] = m;
            }
        }
        while (size > 0) {
            int callee = work[--size];
            for (int caller : callers[callee]) {
                if (!found[caller]) {
                    found[caller] = true;
                    work[size++] = caller;
                }
            }
        }
        return found;
    }

    /** Inverts the call graph: each method's callers. */
    private static int[][] callersOf(int[][] callees) {
        int[] callerCount = new int[callees.length];
        for (int[] called : callees) {
            for (int callee : called) {
                callerCount[callee]++;
            }
        }
        int[][] callers = new int[callees.length][];
        for (int m = 0; m < callees.length; m++) {
            callers[m] = new int[callerCount[m]];
        }
        int[] filled = new int[callees.length];
        for (int m = 0; m < callees.length; m++) {
            for (int callee : callees[m]) {
                callers[callee][filled[callee]++] = m;
            }
        }
        return callers;
    }

    /**
     * For every method that is not {@code any}, adds the writes of everything it may call. Such a
     * method only calls methods that are not {@code any} either, so those can be skipped. Uses an
     * iterative Tarjan's algorithm (like the Python tool's {@code close_over_callees}): each
     * strongly connected component gets one shared set, computed after all the components it
     * calls.
     */
    private static void closeOverCallees(int[][] callees, boolean[] any, BitSet[] written) {
        int n = callees.length;
        int[] index = new int[n]; // visit order, -1 if not visited yet
        int[] low = new int[n]; // lowest index reachable within the component
        Arrays.fill(index, -1);
        boolean[] onStack = new boolean[n];
        int[] stack = new int[n]; // visited methods whose component isn't finished
        int stackSize = 0;
        int[] work = new int[n]; // the current DFS path
        int[] next = new int[n]; // next callee to visit, per method
        int[] group = new int[n]; // members of the component being finished
        int[] groupOf = new int[n];
        Arrays.fill(groupOf, -1);
        int groups = 0;
        int visited = 0;

        for (int root = 0; root < n; root++) {
            if (any[root] || index[root] >= 0) {
                continue;
            }
            int workSize = 0;
            index[root] = low[root] = visited++;
            stack[stackSize++] = root;
            onStack[root] = true;
            next[root] = 0;
            work[workSize++] = root;
            while (workSize > 0) {
                int m = work[workSize - 1];
                boolean descended = false;
                while (next[m] < callees[m].length) {
                    int c = callees[m][next[m]++];
                    if (index[c] < 0) { // descend into c, come back to m later
                        index[c] = low[c] = visited++;
                        stack[stackSize++] = c;
                        onStack[c] = true;
                        next[c] = 0;
                        work[workSize++] = c;
                        descended = true;
                        break;
                    }
                    if (onStack[c]) {
                        low[m] = Math.min(low[m], index[c]);
                    }
                }
                if (descended) {
                    continue;
                }
                // All callees of m are done.
                workSize--;
                if (workSize > 0) {
                    int caller = work[workSize - 1];
                    low[caller] = Math.min(low[caller], low[m]);
                }
                if (low[m] == index[m]) { // m is the root of a finished component
                    int members = 0;
                    int member;
                    do {
                        member = stack[--stackSize];
                        onStack[member] = false;
                        groupOf[member] = groups;
                        group[members++] = member;
                    } while (member != m);
                    BitSet joined = new BitSet();
                    for (int i = 0; i < members; i++) {
                        joined.or(written[group[i]]);
                        for (int c : callees[group[i]]) {
                            if (groupOf[c] != groups) {
                                joined.or(written[c]);
                            }
                        }
                    }
                    for (int i = 0; i < members; i++) {
                        written[group[i]] = joined;
                    }
                    groups++;
                }
            }
        }
    }
}
