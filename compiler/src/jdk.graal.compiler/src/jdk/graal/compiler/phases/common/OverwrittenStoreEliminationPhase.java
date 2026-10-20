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
 * Removes the field stores that every path overwrites, through the same reference, before
 * anything may read the field, before the method may leave, and before anything that may throw.
 * Such a store is dead in Java: no execution can observe its value, not even a handler up the
 * stack, since nothing between the two stores can throw.
 *
 * From each store, the phase follows the control flow forward, through the nodes it knows to be
 * harmless: branches, merges, loop entries and back edges, and accesses to other fields. A path
 * ends well at a store to the same field through the same reference. Any other node ends the
 * search with the store kept: a read of the field, a store to it through another reference, a
 * call, anything with an exception edge, an allocation (which may run out of memory), a return,
 * an unwind, a deoptimization, or any node the phase does not know. A loop that neither reads nor
 * overwrites the field adds nothing, as its exits are followed too.
 *
 * Accesses whose {@link FieldLocationIdentity field locations} carry different partitions, as a
 * points-to analysis can give them, are taken never to touch the same object; without partitions,
 * any two accesses to one field may.
 *
 * A reference is the same at both stores when it is the same value. A value defined in a loop
 * changes from one iteration to the next, so a path through a back edge does not count an
 * overwrite through such a reference: the search keeps the store instead.
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
        Object mine = store.getLocationIdentity() instanceof FieldLocationIdentity location ? location.getPartition() : null;
        Object theirs = other.getLocationIdentity() instanceof FieldLocationIdentity location ? location.getPartition() : null;
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
