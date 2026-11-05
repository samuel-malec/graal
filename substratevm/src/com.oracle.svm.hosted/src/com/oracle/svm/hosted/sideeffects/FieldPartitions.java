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
 * The partition of the objects each access to a field may touch, as the tool says (accesses.txt),
 * when it tells objects apart: an access gets the location of the field in its partition.
 */
final class FieldPartitions {
    /**
     * Where an access is, a tab, and its field -> its partition.
     */
    private final Map<String, String> located = new HashMap<>();
    /**
     * Control: a method, as the export names it, in which different references are claimed never
     * to meet.
     */
    private final String claimNoAliasing;

    FieldPartitions(String claimNoAliasing) {
        this.claimNoAliasing = claimNoAliasing;
    }

    /** Reads each access's partition: where it is, a tab, its field, a tab, its partition. */
    void read(Path accesses) throws IOException {
        for (String line : Files.readAllLines(accesses)) {
            String[] parts = line.split("\t", -1);
            located.put(parts[0] + "\t" + parts[1], parts[2]);
        }
    }

    boolean isEmpty() {
        return located.isEmpty();
    }

    /**
     * Gives each access to a field the location of its partition, when the facts give every
     * access to the field one, and reports the partitions each such field got.
     *
     * @return the fields given partitions
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
                String at = PointsToExport.position(access.getNodeSourcePosition());
                String found = at == null || access.getLocationIdentity().isImmutable() || access.ordersMemoryAccesses() ? null
                                : Names.sitesOf(at).stream().map(site -> located.get(site + "\t" + field.getKey())).filter(Objects::nonNull).findFirst().orElse(null);
                partitions.add(found == null || !split ? found : found + "#" + reference(access));
            }
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

    /**
     * The reference an access goes through, for the split: a parameter, or any other value.
     */
    @SuppressWarnings("deprecation") // a node's id, only to tell values of this graph apart
    private static String reference(AccessFieldNode access) {
        return GraphUtil.unproxify(access.object()) instanceof ParameterNode parameter ? "param" + parameter.index() : "v" + access.object().getId();
    }
}
