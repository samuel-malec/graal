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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;

import com.oracle.graal.pointsto.export.PointsToExport;

import jdk.graal.compiler.nodes.FieldLocationIdentity;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.java.AccessFieldNode;
import jdk.graal.compiler.nodes.util.GraphUtil;

/**
 * With object-field partitions: gives each field access the location of its partition, as the
 * tool's accesses.txt says (which groups of objects each access may touch).
 */
final class FieldPartitions {
    /** Position, a tab, and the field, mapped to the access's partition. */
    private final Map<String, String> located = new HashMap<>();
    /** Test only: a method (as the export names it) in which different references are claimed never to point to the same object. */
    private final String claimNoAliasing;

    FieldPartitions(String claimNoAliasing) {
        this.claimNoAliasing = claimNoAliasing;
    }

    /** Reads accesses.txt: per line the position, field and partition, tab-separated. */
    void read(Path accesses) throws IOException {
        for (String line : Files.readAllLines(accesses)) {
            String[] parts = line.split("\t", -1);
            located.put(parts[0] + "\t" + parts[1], parts[2]);
        }
    }

    /** Whether no access has a partition (field partitioning only). */
    boolean isEmpty() {
        return located.isEmpty();
    }

    /**
     * Gives each access to a field its partitioned location, but only if every access to that field in
     * the graph has a partition, and reports the partitions each field got.
     *
     * @return the fields that were partitioned
     */
    Set<String> partition(StructuredGraph graph, List<String> report) {
        boolean split = Names.exportName(graph.method()).equals(claimNoAliasing);
        Map<String, List<AccessFieldNode>> byField = new TreeMap<>();
        for (AccessFieldNode access : graph.getNodes().filter(AccessFieldNode.class)) {
            byField.computeIfAbsent(Names.fieldName(access.field()), k -> new ArrayList<>()).add(access);
        }
        Set<String> partitioned = new HashSet<>();
        for (Map.Entry<String, List<AccessFieldNode>> field : byField.entrySet()) {
            List<String> partitions = new ArrayList<>();
            for (AccessFieldNode access : field.getValue()) {
                String found = partitionOf(access, field.getKey());
                partitions.add(found == null || !split ? found : found + "#" + reference(access));
            }
            // If any access lacks a partition, the whole field stays unpartitioned; likewise if every
            // partition is the whole field.
            if (partitions.contains(null) || partitions.stream().allMatch(field.getKey()::equals)) {
                continue;
            }
            for (int i = 0; i < partitions.size(); i++) {
                field.getValue().get(i).setLocationIdentity(new FieldLocationIdentity(field.getValue().get(i).field(), false, partitions.get(i)));
            }
            partitioned.add(field.getKey());
            report.add(String.format("%s in %s", Names.shortField(field.getKey()),
                            new TreeSet<>(partitions).stream().map(p -> p.contains("@") ? p.substring(p.indexOf('@')) : p).collect(Collectors.joining(" "))));
        }
        return partitioned;
    }

    /** An access's partition, by the first of its positions in accesses.txt; null without a position, for immutable or volatile accesses. */
    private String partitionOf(AccessFieldNode access, String field) {
        String at = PointsToExport.position(access.getNodeSourcePosition());
        if (at == null || access.getLocationIdentity().isImmutable() || access.ordersMemoryAccesses()) {
            return null;
        }
        return Names.sitesOf(at).stream().map(site -> located.get(site + "\t" + field)).filter(Objects::nonNull).findFirst().orElse(null);
    }

    /** The reference an access goes through, for the no-aliasing test claim: a parameter or any other value. */
    @SuppressWarnings("deprecation") // a node's id, only to tell values of this graph apart
    private static String reference(AccessFieldNode access) {
        return GraphUtil.unproxify(access.object()) instanceof ParameterNode parameter ? "param" + parameter.index() : "v" + access.object().getId();
    }
}
