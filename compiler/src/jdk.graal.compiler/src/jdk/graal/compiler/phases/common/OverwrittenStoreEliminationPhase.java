/*
 * Copyright (c) 2026, Oracle and/or its affiliates. All rights reserved.
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
package jdk.graal.compiler.phases.common;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.graph.NodeBitMap;
import jdk.graal.compiler.nodes.AbstractBeginNode;
import jdk.graal.compiler.nodes.AbstractEndNode;
import jdk.graal.compiler.nodes.FieldLocationIdentity;
import jdk.graal.compiler.nodes.FixedNode;
import jdk.graal.compiler.nodes.GraphState;
import jdk.graal.compiler.nodes.IfNode;
import jdk.graal.compiler.nodes.LoopBeginNode;
import jdk.graal.compiler.nodes.LoopEndNode;
import jdk.graal.compiler.nodes.ParameterNode;
import jdk.graal.compiler.nodes.PhiNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.cfg.ControlFlowGraph;
import jdk.graal.compiler.nodes.cfg.HIRBlock;
import jdk.graal.compiler.nodes.extended.SwitchNode;
import jdk.graal.compiler.nodes.extended.ValueAnchorNode;
import jdk.graal.compiler.nodes.java.AccessFieldNode;
import jdk.graal.compiler.nodes.java.LoadFieldNode;
import jdk.graal.compiler.nodes.java.StoreFieldNode;
import jdk.graal.compiler.nodes.util.GraphUtil;
import jdk.graal.compiler.phases.Phase;
import jdk.vm.ci.meta.ResolvedJavaField;

/**
 * Removes a field store when every path overwrites it, through the same reference, before the
 * field can be read, before the method can return, and before anything can throw. No execution
 * can observe such a store, not even an exception handler further up the stack.
 * <p>
 * From each store the phase walks the control flow forward, passing only nodes it knows are
 * harmless: branches, merges, loop entries and back edges, and accesses to other fields. A path
 * succeeds at a store to the same field through the same reference. Anything else keeps the
 * store: a read of the field, a store to it through another reference, a call, a node with an
 * exception edge, an allocation (it may throw OutOfMemoryError), a return, an unwind, a
 * deoptimization, or any unknown node.
 * <p>
 * Two accesses whose field locations have different partitions
 * ({@link FieldLocationIdentity#getPartition()}) are taken to touch different objects. Without
 * partitions, any two accesses to one field may touch the same object.
 * <p>
 * "The same reference" means the same value. A value defined inside a loop can differ between
 * iterations, so an overwrite reached through a back edge does not count for such a value.
 */
public class OverwrittenStoreEliminationPhase extends Phase {

    @Override
    public Optional<NotApplicable> notApplicableTo(GraphState graphState) {
        return ALWAYS_APPLICABLE;
    }

    @Override
    protected void run(StructuredGraph graph) {
        for (StoreFieldNode store : overwrittenStores(graph)) {
            GraphUtil.removeFixedWithUnusedInputs(store);
        }
    }

    /**
     * The stores of the graph that every path overwrites before anything may observe them. They
     * are found before any is removed: removing one leaves the others overwritten.
     */
    public static List<StoreFieldNode> overwrittenStores(StructuredGraph graph) {
        List<StoreFieldNode> found = new ArrayList<>();
        ControlFlowGraph cfg = null;
        for (StoreFieldNode store : graph.getNodes().filter(StoreFieldNode.class)) {
            if (store.ordersMemoryAccesses()) {
                continue;
            }
            if (cfg == null) {
                cfg = ControlFlowGraph.newBuilder(graph).connectBlocks(true).computeLoops(true).build();
            }
            if (isOverwritten(store, cfg)) {
                found.add(store);
            }
        }
        return found;
    }

    private static boolean isOverwritten(StoreFieldNode store, ControlFlowGraph cfg) {
        ResolvedJavaField field = store.field();
        ValueNode reference = reference(store);
        boolean changesInLoops = reference != null && changesInLoops(reference, cfg);
        NodeBitMap seen = store.graph().createNodeBitMap();
        Deque<FixedNode> work = new ArrayDeque<>();
        push(store.next(), work, seen);
        while (!work.isEmpty()) {
            FixedNode node = work.pop();
            if (node instanceof AccessFieldNode access && !access.ordersMemoryAccesses() && (node instanceof StoreFieldNode || node instanceof LoadFieldNode)) {
                if (!access.field().equals(field) || inOtherPartition(store, access)) {
                    push(access.next(), work, seen);
                } else if (!(node instanceof StoreFieldNode) || !Objects.equals(reference(access), reference)) {
                    return false; // a read, or a store through a reference that may be another object
                }
                // else: overwritten on this path
            } else if (node instanceof LoopEndNode end) {
                if (changesInLoops) {
                    return false;
                }
                push(end.loopBegin(), work, seen);
            } else if (node instanceof AbstractEndNode end) {
                push(end.merge(), work, seen);
            } else if (node instanceof IfNode || node instanceof SwitchNode) {
                for (Node successor : node.successors()) {
                    push((FixedNode) successor, work, seen);
                }
            } else if (node instanceof AbstractBeginNode begin) {
                push(begin.next(), work, seen);
            } else if (node instanceof ValueAnchorNode anchor) {
                push(anchor.next(), work, seen);
            } else {
                return false; // it may read the field, leave the method or throw
            }
        }
        return true;
    }

    private static void push(FixedNode node, Deque<FixedNode> work, NodeBitMap seen) {
        if (node != null && !seen.isMarked(node)) {
            seen.mark(node);
            work.push(node);
        }
    }

    /** The reference an access goes through, past proxies; null for a static field. */
    private static ValueNode reference(AccessFieldNode access) {
        return access.object() == null ? null : GraphUtil.unproxify(access.object());
    }

    /** Whether points-to partitions tell the two accesses apart. */
    private static boolean inOtherPartition(AccessFieldNode store, AccessFieldNode other) {
        String mine = store.getLocationIdentity() instanceof FieldLocationIdentity location ? location.getPartition() : null;
        String theirs = other.getLocationIdentity() instanceof FieldLocationIdentity location ? location.getPartition() : null;
        return mine != null && theirs != null && !mine.equals(theirs);
    }

    /**
     * Whether the value may differ between iterations of a loop: a phi of a loop, or anything
     * defined inside one. Parameters and constants never change; any other floating value is taken
     * to change.
     */
    private static boolean changesInLoops(ValueNode value, ControlFlowGraph cfg) {
        if (value instanceof ParameterNode || value.isConstant()) {
            return false;
        }
        Node place = value instanceof PhiNode phi ? phi.merge() : value instanceof FixedNode ? value : null;
        if (place == null || place instanceof LoopBeginNode) {
            return true;
        }
        HIRBlock block = cfg.blockFor(place);
        return block == null || block.getLoop() != null;
    }
}
