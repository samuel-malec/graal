package com.oracle.graal.pointsto.export;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.TreeSet;

import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.flow.InvokeTypeFlow;
import com.oracle.graal.pointsto.flow.MethodFlowsGraph;
import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.flow.context.object.AnalysisObject;
import com.oracle.graal.pointsto.flow.context.object.ConstantContextSensitiveObject;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisField;
import com.oracle.graal.pointsto.meta.PointsToAnalysisMethod;
import com.oracle.graal.pointsto.typestate.TypeState;
import com.oracle.graal.pointsto.typestore.ArrayElementsTypeStore;
import com.oracle.graal.pointsto.typestore.FieldTypeStore;

/**
 * Which objects of the points-to analysis another thread may reach. An object is shared when
 * a static field, an object in the image heap, a thread, a reference the reference handler
 * thread processes, or an argument of a call the analysis can't see all of can reach it, through
 * the fields and array elements the analysis says may hold it. Every other object is only ever
 * reached by the thread that made it.
 *
 * A call the analysis can't see all of reaches a method the facts can't describe whole: one
 * without facts, such as a native, or one with an effect or a call the facts can't name. What
 * such a method does with its arguments, and what the analysis then misses after it, are
 * unknown.
 * Without facts for {@code Thread.currentThread}, the standalone analysis never sees
 * {@code new Thread(task)} store the task, for instance.
 *
 * A field whose flow saturated may hold any object of its declared type, so then every object
 * of that type is shared once the field's object is. With aliased array flows, the default, all
 * object arrays share one elements flow: an object stored in any array is shared once any array
 * is.
 */
final class ThreadEscape {

    private final PointsToAnalysis bb;
    /** Every object some flow of a reachable method, or a static field, may hold. */
    private final Set<AnalysisObject> known = new LinkedHashSet<>();
    private final Set<AnalysisObject> shared = new HashSet<>();
    private final Deque<AnalysisObject> work = new ArrayDeque<>();
    /** The declared types of the saturated flows a shared object reaches: all their objects are shared. */
    private final Set<AnalysisType> anyOf = new HashSet<>();

    private ThreadEscape(PointsToAnalysis bb) {
        this.bb = bb;
    }

    /**
     * The names of the shared objects, as {@link GraphExport.PointsTo#objectName} gives them.
     * {@code described} says whether the facts describe a method whole.
     */
    static TreeSet<String> sharedObjects(PointsToAnalysis bb, AnalysisUniverse universe, java.util.function.Predicate<AnalysisMethod> described) {
        ThreadEscape escape = new ThreadEscape(bb);
        escape.run(universe, described);
        TreeSet<String> names = new TreeSet<>();
        for (AnalysisObject object : escape.shared) {
            names.add(GraphExport.PointsTo.objectName(object));
        }
        return names;
    }

    private void run(AnalysisUniverse universe, java.util.function.Predicate<AnalysisMethod> described) {
        AnalysisType thread = bb.getMetaAccess().lookupJavaType(Thread.class);
        AnalysisType reference = bb.getMetaAccess().lookupJavaType(java.lang.ref.Reference.class);
        Set<AnalysisMethod> incomplete = incomplete(universe, described);
        for (AnalysisMethod method : universe.getMethods()) {
            if (!analysed(method)) {
                continue;
            }
            for (MethodFlowsGraph graph : ((PointsToAnalysisMethod) method).getTypeFlow().getFlows()) {
                for (TypeFlow<?> flow : graph.flows()) {
                    collect(flow, known);
                }
                for (InvokeTypeFlow invoke : graph.getInvokes()) {
                    if (invoke.getOriginalCallees().stream().anyMatch(incomplete::contains)) {
                        for (TypeFlow<?> argument : invoke.getActualParameters()) {
                            if (argument != null) {
                                reach(argument);
                            }
                        }
                    }
                }
            }
        }
        for (AnalysisField field : universe.getFields()) {
            if (field.isStatic() && field instanceof PointsToAnalysisField pointsTo) {
                reach(pointsTo.getStaticFieldFlow(), field.getType());
            }
        }
        for (AnalysisObject object : known) {
            if (object instanceof ConstantContextSensitiveObject || thread.isAssignableFrom(object.type()) || reference.isAssignableFrom(object.type())) {
                share(object);
            }
        }
        Set<AnalysisType> expanded = new HashSet<>();
        do {
            while (!work.isEmpty()) {
                AnalysisObject object = work.pop();
                for (FieldTypeStore store : object.getExistingInstanceFieldTypeStores()) {
                    reach(store.writeFlow(), store.field().getType());
                }
                ArrayElementsTypeStore elements = object.type().isArray() ? object.getArrayElementsTypeStore() : null;
                if (elements != null && elements.writeFlow() != null) {
                    reach(elements.writeFlow(), object.type().getComponentType());
                }
            }
            for (AnalysisType type : new HashSet<>(anyOf)) {
                if (expanded.add(type)) {
                    for (AnalysisObject object : known) {
                        if (type.isAssignableFrom(object.type())) {
                            share(object);
                        }
                    }
                }
            }
        } while (!work.isEmpty());
    }

    private static boolean analysed(AnalysisMethod method) {
        return method.isReachable() && method instanceof PointsToAnalysisMethod ptm && ptm.getTypeFlow().flowsGraphCreated();
    }

    /** The methods the facts don't describe whole, and every method that may call one, directly or not. */
    private static Set<AnalysisMethod> incomplete(AnalysisUniverse universe, java.util.function.Predicate<AnalysisMethod> described) {
        java.util.Map<AnalysisMethod, Set<AnalysisMethod>> callers = new java.util.HashMap<>();
        Deque<AnalysisMethod> work = new ArrayDeque<>();
        Set<AnalysisMethod> found = new HashSet<>();
        for (AnalysisMethod method : universe.getMethods()) {
            if (!analysed(method)) {
                continue;
            }
            if (!described.test(method) && found.add(method)) {
                work.push(method);
            }
            for (InvokeTypeFlow invoke : ((PointsToAnalysisMethod) method).getTypeFlow().getInvokes()) {
                for (AnalysisMethod callee : invoke.getOriginalCallees()) {
                    callers.computeIfAbsent(callee, k -> new HashSet<>()).add(method);
                    if ((!analysed(callee) || !described.test(callee)) && found.add(callee)) {
                        work.push(callee);
                    }
                }
            }
        }
        while (!work.isEmpty()) {
            for (AnalysisMethod caller : callers.getOrDefault(work.pop(), Set.of())) {
                if (found.add(caller)) {
                    work.push(caller);
                }
            }
        }
        return found;
    }

    private void collect(TypeFlow<?> flow, Set<AnalysisObject> into) {
        TypeState state = flow.isSaturated() ? null : flow.getState();
        if (state != null && !state.isPrimitive()) {
            for (AnalysisObject object : state.objects(bb)) {
                into.add(object);
            }
        }
    }

    /** What a flow may hold is shared; for a saturated flow, any object of its declared type. */
    private void reach(TypeFlow<?> flow, AnalysisType declared) {
        if (flow.isSaturated()) {
            if (declared != null && !declared.isPrimitive()) {
                anyOf.add(declared);
            }
            return;
        }
        Set<AnalysisObject> held = new LinkedHashSet<>();
        collect(flow, held);
        known.addAll(held);
        held.forEach(this::share);
    }

    private void reach(TypeFlow<?> flow) {
        reach(flow, flow.getDeclaredType());
    }

    private void share(AnalysisObject object) {
        if (shared.add(object)) {
            work.push(object);
        }
    }
}
