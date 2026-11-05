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

import java.util.ArrayList;
import java.util.List;

import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.util.GraphUtil;
import jdk.graal.compiler.phases.common.OverwrittenStoreEliminationPhase;

/**
 * Runs Graal's {@link OverwrittenStoreEliminationPhase} on one of the program's methods, after the
 * analysis is applied (so with its partitions), and reports each store it removes.
 */
final class EliminateOverwrittenStoresPhase extends TimedPhase {
    private final String program;
    private final CompiledCodeCounts counts;

    EliminateOverwrittenStoresPhase(StepTimes times, String program, CompiledCodeCounts counts) {
        super(times, "eliminate overwritten stores");
        this.program = program;
        this.counts = counts;
    }

    @Override
    protected void runOn(StructuredGraph graph) {
        if (!Names.inProgram(graph.method(), program)) {
            return;
        }
        List<String> removed = new ArrayList<>();
        for (StoreFieldNode store : OverwrittenStoreEliminationPhase.overwrittenStores(graph)) {
            removed.add(String.format("overwritten store to %s at bci %d removed", Names.shortField(Names.fieldName(store.field())),
                            store.getNodeSourcePosition() != null ? store.getNodeSourcePosition().getBCI() : -1));
            GraphUtil.removeFixedWithUnusedInputs(store);
        }
        if (!removed.isEmpty()) {
            counts.addChanges(graph, removed);
        }
        graph.getDebug().dump(DebugContext.BASIC_LEVEL, graph, "After eliminating overwritten stores");
    }
}
