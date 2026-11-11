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
 * What each method, or anything it calls, may write: the kill set of a call to it, worked out in
 * the build from the facts the export collects, as the tool's {@code effects.kills} works it out
 * from the export with partitions by field and no effect left out. The answer is what the tool
 * writes to kills.txt, a line per method: its name, a tab, and the partitions it may write, a
 * field's or an array kind's name, {@code init} if it allocates, the VM's state it writes, joined
 * by commas; or {@code any}.
 * <p>
 * A method's kill set is {@code any} if it, or anything it calls, has an effect the facts can't
 * name, synchronizes in a way that may order this thread with another, makes a call the analysis
 * could not resolve, or calls a method the export has no facts for. Every other method calls only
 * methods like itself, and may write what they and it write.
 */
final class KillSetComputation {
    static final String ANY = "any";
    static final String INIT = "init";

    // The pseudo-objects the export names, as the tool's signatures.py reads them: an object the
    // analysis can't name, an access whose receiver is always null, and a class's static fields.
    private static final String UNKNOWN_OBJECT = "?";
    private static final String NO_OBJECT = "null";
    private static final String STATICS = ".<statics>";

    private KillSetComputation() {
    }

    /**
     * The kill set of every method the export has facts for, in the order of their names.
     * {@code shared} is the objects another thread may reach, null when thread escape did not run:
     * then every acquire and release may order this thread with another.
     */
    static List<String> lines(PointsToExport.Facts facts, Set<String> shared) {
        TreeSet<String> names = new TreeSet<>(facts.analysed);
        names.addAll(facts.callees.keySet());
        String[] methods = names.toArray(new String[0]);
        Map<String, Integer> method = new HashMap<>();
        for (int m = 0; m < methods.length; m++) {
            method.put(methods[m], m);
        }

        // Numbered in the order of their names, so that a set lists them as the tool sorts them.
        TreeSet<String> partitionNames = new TreeSet<>();
        for (String m : methods) {
            partitionNames.addAll(facts.writes.getOrDefault(m, new TreeSet<>()));
            partitionNames.addAll(facts.vmWrites.getOrDefault(m, new TreeSet<>()));
        }
        partitionNames.add(INIT);
        String[] partitions = partitionNames.toArray(new String[0]);
        Map<String, Integer> partition = new HashMap<>();
        for (int p = 0; p < partitions.length; p++) {
            partition.put(partitions[p], p);
        }

        int[][] callees = new int[methods.length][];
        BitSet[] written = new BitSet[methods.length];
        boolean[] blocked = new boolean[methods.length];
        for (int m = 0; m < methods.length; m++) {
            String name = methods[m];
            TreeSet<String> called = facts.callees.getOrDefault(name, new TreeSet<>());
            int[] ids = new int[called.size()];
            int known = 0;
            boolean withoutFacts = false;
            for (String callee : called) {
                Integer id = method.get(callee);
                if (id == null) {
                    withoutFacts = true;
                } else {
                    ids[known++] = id;
                }
            }
            callees[m] = Arrays.copyOf(ids, known);
            blocked[m] = !facts.unknown.getOrDefault(name, new TreeSet<>()).isEmpty() ||
                            orders(facts.acquires.get(name), facts.locks.get(name), shared) ||
                            orders(facts.releases.get(name), facts.locks.get(name), shared) ||
                            !facts.unresolved.getOrDefault(name, new TreeSet<>()).isEmpty() || withoutFacts;
            BitSet own = new BitSet(partitions.length);
            for (String p : facts.writes.getOrDefault(name, new TreeSet<>())) {
                own.set(partition.get(p));
            }
            for (String p : facts.vmWrites.getOrDefault(name, new TreeSet<>())) {
                own.set(partition.get(p));
            }
            if (facts.allocates.contains(name)) {
                own.set(partition.get(INIT));
            }
            written[m] = own;
        }

        boolean[] any = reaching(callees, blocked);
        closeOverCallees(callees, any, written);

        List<String> lines = new ArrayList<>(methods.length);
        StringBuilder line = new StringBuilder();
        for (int m = 0; m < methods.length; m++) {
            line.setLength(0);
            line.append(methods[m]).append('\t');
            if (any[m]) {
                line.append(ANY);
            } else {
                String separator = "";
                for (int p = written[m].nextSetBit(0); p >= 0; p = written[m].nextSetBit(p + 1)) {
                    line.append(separator).append(partitions[p]);
                    separator = ",";
                }
            }
            lines.add(line.toString());
        }
        return lines;
    }

    /**
     * Whether any of a method's acquires or releases may order this thread with another: one on a
     * lock or a volatile field that another thread may reach, or one the export has no objects for.
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
                if (!object.equals(NO_OBJECT) && (shared == null || object.equals(UNKNOWN_OBJECT) || object.endsWith(STATICS) || shared.contains(object))) {
                    return true;
                }
            }
        }
        return false;
    }

    /** The blocked methods, and every method that calls one, directly or not. */
    private static boolean[] reaching(int[][] callees, boolean[] blocked) {
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

    /**
     * Adds to the set of each method that is not {@code any} the sets of every method it may call,
     * directly or not. Methods that call each other end with one set; their callees outside the
     * group are done before them (Tarjan's algorithm, without recursion, as the tool's
     * close_over_callees). A method that is not {@code any} calls only methods that are not.
     */
    private static void closeOverCallees(int[][] callees, boolean[] any, BitSet[] written) {
        int n = callees.length;
        int[] index = new int[n];
        int[] low = new int[n];
        Arrays.fill(index, -1);
        boolean[] onStack = new boolean[n];
        int[] stack = new int[n];
        int stackSize = 0;
        int[] work = new int[n];
        int[] next = new int[n]; // the position in a method's callees that its visit has reached
        int[] group = new int[n];
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
                    if (index[c] < 0) {
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
                workSize--;
                if (workSize > 0) {
                    int caller = work[workSize - 1];
                    low[caller] = Math.min(low[caller], low[m]);
                }
                if (low[m] == index[m]) {
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
