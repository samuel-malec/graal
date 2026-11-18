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
 * The kill set of a call to each method: what the method, or anything it may call, may write. The
 * image builder works it out from the facts the export collects, the same way the tool's
 * {@code effects.kills} works it out from an export (partitions by field, no effect left out), and
 * gives the same lines as the tool's kills.txt: the method, a tab, and either {@code any} or the
 * partitions it may write joined by commas (a field's or an array kind's name, {@code init} if it
 * allocates, the VM's own locations).
 * <p>
 * A method's kill set is {@code any} if it, or anything it may call, has an effect the facts can't
 * name, synchronization that may order this thread with another, a call the analysis couldn't
 * resolve, or a call to a method the export has no facts for. Every other method only calls
 * methods like itself, so its kill set is what it and they write.
 */
final class KillSetComputation {
    static final String ANY = "any";
    static final String INIT = "init";

    // The stand-in objects the export names, as the tool's signatures.py reads them: an object the
    // analysis can't name, the object of an access whose reference is always null, and a class's
    // static fields.
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
        Map<String, Integer> method = positions(methods);

        // Numbered in the order of their names, so that a set lists them as the tool sorts them.
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

    /** The numbers of the called methods the export has facts for, in the order of their names. */
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
     * Whether the method by itself makes its kill set everything, as the tool's
     * {@code effects.kills.blocks} says: an unknown effect, synchronization that may order this
     * thread with another, an unresolved call, or a call to a method without facts.
     */
    private static boolean blocks(PointsToExport.Facts facts, String method, Set<String> shared, boolean callsWithoutFacts) {
        return !facts.unknown.getOrDefault(method, new TreeSet<>()).isEmpty() ||
                        orders(facts.acquires.get(method), facts.locks.get(method), shared) ||
                        orders(facts.releases.get(method), facts.locks.get(method), shared) ||
                        !facts.unresolved.getOrDefault(method, new TreeSet<>()).isEmpty() || callsWithoutFacts;
    }

    /** The partitions the method itself writes, by their numbers. */
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

    /** A method's line of kills.txt. */
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
     * Whether any of a method's acquires or releases may order this thread with another: one on a
     * lock or a volatile field another thread may reach, or one the export names no objects for.
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
     * Whether another thread may reach the object, as the tool's {@code shared_object} says: one the
     * analysis can't name, a class's static fields, an object thread escape found shared, or any
     * object when thread escape did not run.
     */
    private static boolean isShared(String object, Set<String> shared) {
        return shared == null || object.equals(UNKNOWN_OBJECT) || object.endsWith(STATICS) || shared.contains(object);
    }

    /** The blocked methods, and every method that may call one, directly or not. */
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

    /** Each method's callers, the other way round from {@code callees}. */
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
     * Adds to the set of each method that is not {@code any} the sets of every method it may call,
     * directly or not; such a method only calls methods that are not {@code any} either. Methods
     * that call each other end with one set. Tarjan's algorithm without recursion, as the tool's
     * {@code close_over_callees}: a group is complete only after every group it calls.
     */
    private static void closeOverCallees(int[][] callees, boolean[] any, BitSet[] written) {
        int n = callees.length;
        int[] index = new int[n]; // the order in which each method was first visited, -1 before
        int[] low = new int[n]; // the lowest index the method reaches inside its group
        Arrays.fill(index, -1);
        boolean[] onStack = new boolean[n];
        int[] stack = new int[n]; // visited methods whose group isn't complete
        int stackSize = 0;
        int[] work = new int[n]; // the current path
        int[] next = new int[n]; // the position in a method's callees that its visit has reached
        int[] group = new int[n]; // the members of the group being completed
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
                    if (index[c] < 0) { // visit it first, then come back to m
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
                // Every callee of m is done.
                workSize--;
                if (workSize > 0) {
                    int caller = work[workSize - 1];
                    low[caller] = Math.min(low[caller], low[m]);
                }
                if (low[m] == index[m]) { // m is its group's first method: the group is complete
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
