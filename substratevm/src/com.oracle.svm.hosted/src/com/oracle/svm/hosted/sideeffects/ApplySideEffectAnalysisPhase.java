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
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.graalvm.word.LocationIdentity;

import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.nodes.Invoke;
import jdk.graal.compiler.nodes.InvokeWithExceptionNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.java.ExceptionObjectNode;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Runs right after Native Image's inliners on each of the program's methods. Gives field accesses
 * their partitions, and narrows each call (and the entry of its exception handler) to what its
 * possible callees may write. Inlined code is included: a call's kill set depends on its targets,
 * not on where the call is.
 */
final class ApplySideEffectAnalysisPhase extends TimedPhase {
    private final KillSets killSets;
    private final FieldPartitions partitions;
    private final String program;
    private final List<String> only;
    private final List<String> skip;
    private final CompiledCodeCounts counts;

    /**
     * @param only narrow calls only in methods with these name prefixes; all methods if empty
     * @param skip don't narrow calls in methods with these prefixes
     */
    ApplySideEffectAnalysisPhase(StepTimes times, KillSets killSets, FieldPartitions partitions, String program, List<String> only, List<String> skip, CompiledCodeCounts counts) {
        super(times, "apply");
        this.killSets = killSets;
        this.partitions = partitions;
        this.program = program;
        this.only = only;
        this.skip = skip;
        this.counts = counts;
    }

    @Override
    protected void runOn(StructuredGraph graph) {
        if (!Names.inProgram(graph.method(), program)) {
            return;
        }
        List<String> calls = new ArrayList<>();
        Set<String> partitioned = partitions.isEmpty() ? Set.of() : partitions.partition(graph, calls);
        boolean narrows = narrowsIn(graph.method());
        for (Node node : graph.getNodes()) {
            if (narrows && node instanceof Invoke invoke && invoke.callTarget() instanceof MethodCallTargetNode target) {
                LocationIdentity[] locations = killSets.killsOf(target, partitioned);
                if (locations != null) {
                    narrow(invoke, locations);
                    calls.add(String.format("%s kills %s", Names.readableName(target.targetMethod()), shown(locations)));
                }
            }
        }
        if (!calls.isEmpty()) {
            Collections.sort(calls);
            counts.listChanges(graph, calls);
        }
        graph.getDebug().dump(DebugContext.BASIC_LEVEL, graph, "After applying the side-effect analysis");
    }

    /** Restricts a call, and its exception handler's entry, to what its callees may write plus the VM state. */
    private void narrow(Invoke invoke, LocationIdentity[] locations) {
        List<LocationIdentity> killed = new ArrayList<>(List.of(locations));
        killed.addAll(killSets.killedByEveryCall());
        invoke.setKilledLocationIdentities(killed.toArray(new LocationIdentity[0]));
        if (invoke instanceof InvokeWithExceptionNode withException && withException.exceptionEdge() instanceof ExceptionObjectNode handler) {
            // The handler runs after the callee threw; before throwing, the callee may have written
            // anything it writes normally.
            handler.setKilledLocationIdentities(killed.toArray(new LocationIdentity[0]));
        }
    }

    /** A call's kill set for counts.txt: short location names, without the VM state. */
    private String shown(LocationIdentity[] locations) {
        LocationIdentity[] set = Invoke.killSet(Arrays.stream(locations).filter(l -> !killSets.isVMState(l)).toArray(LocationIdentity[]::new));
        return set.length == 0 ? "nothing" : Arrays.stream(set).map(l -> Names.simpleName(l.toString())).collect(Collectors.joining(" "));
    }

    /** Whether calls in this method are narrowed, given the only/skip options. */
    private boolean narrowsIn(ResolvedJavaMethod method) {
        String name = Names.exportName(method);
        return (only.isEmpty() || only.stream().anyMatch(name::startsWith)) && skip.stream().noneMatch(name::startsWith);
    }
}
