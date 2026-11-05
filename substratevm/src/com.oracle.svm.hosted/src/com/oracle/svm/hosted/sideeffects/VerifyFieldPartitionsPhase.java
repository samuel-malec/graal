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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.FieldLocationIdentity;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.memory.MemoryAccess;
import jdk.vm.ci.meta.ResolvedJavaField;

/**
 * Stops the build if a graph has accesses to one field both with and without a partition, as a
 * phase that makes a new access after the partitioning could: their locations would not overlap,
 * and nothing would order them.
 */
final class VerifyFieldPartitionsPhase extends TimedPhase {
    VerifyFieldPartitionsPhase(StepTimes times) {
        super(times, "verify partitions");
    }

    @Override
    protected void runOn(StructuredGraph graph) {
        Map<ResolvedJavaField, Set<Boolean>> kinds = new HashMap<>();
        for (Node node : graph.getNodes()) {
            if (node instanceof MemoryAccess access && access.getLocationIdentity() instanceof FieldLocationIdentity field && !field.isImmutable()) {
                kinds.computeIfAbsent(field.getField(), k -> new HashSet<>()).add(field.getPartition() != null);
            }
        }
        kinds.forEach((field, partitioned) -> {
            if (partitioned.size() > 1) {
                throw new IllegalStateException(graph.method().format("%H.%n") + " accesses " + Names.fieldName(field) + " both with and without a partition");
            }
        });
    }
}
