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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.flow.LoadFieldTypeFlow;
import com.oracle.graal.pointsto.flow.OffsetLoadTypeFlow;
import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.flow.context.object.AnalysisObject;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.typestate.TypeState;

/**
 * Says what a points-to flow may hold, even after it saturated. An unsaturated flow holds the
 * objects of its state, filtered by its declared type. For a saturated flow the analysis stopped
 * tracking contents, so they are rebuilt from the flows that feed it (recorded with
 * {@code -H:+TrackInputFlows}): exact inputs as they are, loads by what was stored into the field
 * or arrays they read, and anything unknown as any object of the declared type.
 */
final class FlowReader {

    /**
     * What some flows may hold: the analysis' states, "any object of a type" (for saturated flows),
     * the places saturated loads read from (resolved once all stores are known), and single objects.
     */
    record Held(List<TypeState> states, List<AnalysisType> any, List<Source> stored, List<AnalysisObject> objects) {

        static final Held NOTHING = new Held(List.of(), List.of(), List.of(), List.of());

        Held(List<TypeState> states, List<AnalysisType> any) {
            this(states, any, List.of(), List.of());
        }

        Held(List<TypeState> states, List<AnalysisType> any, List<Source> stored) {
            this(states, any, stored, List.of());
        }

        boolean isNothing() {
            return states.isEmpty() && any.isEmpty() && stored.isEmpty() && objects.isEmpty();
        }

        /** The objects named by the states and the list. */
        Iterable<AnalysisObject> objectsIn(PointsToAnalysis bb) {
            List<AnalysisObject> all = new ArrayList<>(objects);
            for (TypeState state : states) {
                for (AnalysisObject object : state.objects(bb)) {
                    all.add(object);
                }
            }
            return all;
        }

        Held with(Held other) {
            if (isNothing()) {
                return other;
            } else if (other.isNothing()) {
                return this;
            }
            List<TypeState> allStates = new ArrayList<>(states);
            allStates.addAll(other.states);
            List<AnalysisType> allAny = new ArrayList<>(any);
            allAny.addAll(other.any);
            List<Source> allStored = new ArrayList<>(stored);
            allStored.addAll(other.stored);
            List<AnalysisObject> allObjects = new ArrayList<>(objects);
            allObjects.addAll(other.objects);
            return new Held(allStates, allAny, allStored, allObjects);
        }
    }

    /**
     * What a saturated load reads: what was stored into a place (a field, all arrays, or a flow's
     * inputs), filtered to objects that have every type the loads along the way require.
     */
    record Source(Object key, List<AnalysisType> filters) {
    }

    /** Cache key for the meet of two type lists. */
    private record Pair(List<AnalysisType> a, List<AnalysisType> b) {
    }

    /**
     * The key for the place "all arrays" in a {@link Source}. The analysis gives all arrays one element
     * flow, so a saturated array load may read what was stored into any array.
     */
    static final Object ARRAYS = new Object();

    /** No type filter: the declared type says nothing, or a place is read as it is. */
    static final List<AnalysisType> NO_TYPES = List.of();

    /** Cache marker for "no object has all these types"; a distinct list that no meet produces. */
    private static final List<AnalysisType> NOBODY = Collections.unmodifiableList(new ArrayList<>());

    // Shared with the thread-escape run this reader serves.
    private final ThreadEscape escape;
    private final PointsToAnalysis bb;
    private final Set<String> assumptions;
    private final boolean readFlows;
    private final AnalysisType objectType;
    private final Pattern explain;
    private final Set<AnalysisObject> shared;
    SharingExplanation why;

    // Caches for type questions that are asked many times.
    /** Meets of pairs of type lists; its size appears in the progress output. */
    final Map<Pair, List<AnalysisType>> meets = new HashMap<>();
    private final Map<Long, Boolean> assignable = new HashMap<>();
    private final Map<AnalysisType, Set<AnalysisType>> subtypes = new HashMap<>();

    /** What each saturated flow rebuilt so far holds. */
    private final Map<TypeFlow<?>, Held> rebuilt = new IdentityHashMap<>();

    /** How many traces of "any object of a type" were printed while explaining (at most 400). */
    private int anyPrinted;

    FlowReader(ThreadEscape escape) {
        this.escape = escape;
        this.bb = escape.bb;
        this.assumptions = escape.assumptions;
        this.readFlows = escape.readFlows;
        this.objectType = escape.objectType;
        this.explain = escape.explain;
        this.shared = escape.shared;
    }

    /** Connects the explanation, created after the reader. */
    void connect(SharingExplanation why) {
        this.why = why;
    }

    /** The same place, for a load that also requires these types; null if no object can have them all. */
    Source narrowed(Source source, List<AnalysisType> others) {
        if (others.isEmpty() || others == source.filters()) {
            return source;
        }
        Pair pair = new Pair(source.filters(), others);
        List<AnalysisType> both = meets.get(pair);
        if (both == null) {
            both = meet(source.filters(), others);
            both = both == null ? NOBODY : both;
            meets.put(pair, both);
        }
        if (both == NOBODY) {
            return null;
        }
        return both.equals(source.filters()) ? source : new Source(source.key(), both);
    }

    /** The types an object needs to have all of both lists, without redundant ones; null if impossible. */
    private List<AnalysisType> meet(List<AnalysisType> a, List<AnalysisType> b) {
        if (a.isEmpty() || a.equals(b)) {
            return b;
        } else if (b.isEmpty()) {
            return a;
        } else if (a.size() == 1 && b.size() == 1) {
            if (assignableTo(a.get(0), b.get(0))) {
                return b;
            } else if (assignableTo(b.get(0), a.get(0))) {
                return a;
            }
        }
        List<AnalysisType> all = new ArrayList<>(a);
        for (AnalysisType type : b) {
            if (!all.contains(type)) {
                all.add(type);
            }
        }
        // A type is redundant if another type in the list is its subtype. Of two types that are each
        // other's subtype, the first is kept.
        List<AnalysisType> kept = new ArrayList<>();
        for (AnalysisType type : all) {
            boolean redundant = false;
            for (AnalysisType other : all) {
                if (other != type && type.isAssignableFrom(other) && !(other.isAssignableFrom(type) && all.indexOf(other) > all.indexOf(type))) {
                    redundant = true;
                    break;
                }
            }
            if (!redundant) {
                kept.add(type);
            }
        }
        for (int i = 0; i < kept.size(); i++) {
            for (int k = i + 1; k < kept.size(); k++) {
                if (noObjectHasBoth(kept.get(i), kept.get(k))) {
                    return null;
                }
            }
        }
        kept.sort((x, y) -> Integer.compare(x.getId(), y.getId()));
        return List.copyOf(kept);
    }

    /** Whether no object can have both types: two unrelated classes, or an array and an interface arrays don't implement. */
    static boolean noObjectHasBoth(AnalysisType x, AnalysisType y) {
        if (x.isAssignableFrom(y) || y.isAssignableFrom(x)) {
            return false;
        }
        if (!x.isInterface() && !y.isInterface()) {
            return true;
        }
        // An array has only the array interfaces.
        AnalysisType other = x.isInterface() ? x : y;
        AnalysisType notInterface = x.isInterface() ? y : x;
        return notInterface.isArray() && !mayBeArray(other);
    }

    /**
     * The flow an access observes. When it saturated, the analysis switches the access to the
     * declared type's flow; the original flow, if there was only one, says more (needs recorded
     * inputs).
     */
    TypeFlow<?> observedBy(TypeFlow<?> access, TypeFlow<?> observed) {
        if (observed == null || !observed.isAllInstantiated() || !bb.trackTypeFlowInputs()) {
            return observed;
        }
        TypeFlow<?> first = null;
        for (TypeFlow<?> observee : access.getObservees()) {
            if (!observee.isAllInstantiated()) {
                if (first != null && first != observee) {
                    return observed;
                }
                first = observee;
            }
        }
        return first != null ? first : observed;
    }

    /** The type filter of a flow: its declared type, unless that says nothing. */
    private List<AnalysisType> filterOf(TypeFlow<?> flow) {
        AnalysisType declared = flow.getDeclaredType();
        return declared == null || declared.isPrimitive() || declared.isJavaLangObject() ? NO_TYPES : List.of(declared);
    }

    /** Whether every object of the type has the filter's type (cached {@code isAssignableFrom}). */
    boolean assignableTo(AnalysisType filter, AnalysisType type) {
        long key = filter.getId() * 0x9E3779B97F4A7C15L + type.getId();
        Boolean known = assignable.get(key);
        if (known == null) {
            known = filter.isAssignableFrom(type);
            assignable.put(key, known);
        }
        return known;
    }

    /** Whether an object of the type has all the filter types. */
    boolean matches(List<AnalysisType> filters, AnalysisType type) {
        for (AnalysisType filter : filters) {
            if (!assignableTo(filter, type)) {
                return false;
            }
        }
        return true;
    }

    /** The type and all its subtypes from the hierarchy; arrays are not included. */
    Set<AnalysisType> subtypesOf(AnalysisType type) {
        Set<AnalysisType> found = subtypes.get(type);
        if (found == null) {
            found = new HashSet<>();
            type.getAllSubtypes().forEach(found::add);
            subtypes.put(type, found);
        }
        return found;
    }

    /** What a value holds of the given types: matching objects, the types it narrows to, and where else it reads from. */
    private Held filtered(Held held, List<AnalysisType> filters) {
        if (filters.isEmpty() || held.isNothing()) {
            return held;
        }
        List<AnalysisObject> objects = new ArrayList<>();
        for (AnalysisObject object : held.objectsIn(bb)) {
            if (matches(filters, object.type())) {
                objects.add(object);
            }
        }
        List<AnalysisType> any = new ArrayList<>();
        narrowAny(any, held.any(), filters);
        List<Source> stored = new ArrayList<>();
        for (Source source : held.stored()) {
            Source narrowed = narrowed(source, filters);
            if (narrowed != null) {
                stored.add(narrowed);
            }
        }
        return new Held(List.of(), any, stored, objects);
    }

    /** Whether any of the objects is an array. */
    static boolean hasArray(Iterable<AnalysisObject> objects) {
        for (AnalysisObject object : objects) {
            if (object.type().isArray()) {
                return true;
            }
        }
        return false;
    }

    /** Adds the types of saturated flows that may hold objects of the requested types. */
    void narrowAny(Collection<AnalysisType> into, Iterable<AnalysisType> any, List<AnalysisType> filters) {
        for (AnalysisType type : any) {
            if (matches(filters, type)) {
                into.add(type);
                continue;
            }
            boolean added = false;
            boolean unrelated = false;
            for (AnalysisType filter : filters) {
                if (type.isAssignableFrom(filter)) {
                    into.add(filter);
                    added = true;
                } else if (!filter.isAssignableFrom(type) && !noObjectHasBoth(type, filter)) {
                    unrelated = true;
                }
            }
            if (!added && unrelated) {
                into.add(type);
            }
        }
    }

    /** Whether the objects may include an array: an array object, or a flow saturated at a type an array may have. */
    boolean mayBeArray(Held held) {
        if (hasArray(held.objectsIn(bb))) {
            return true;
        }
        for (AnalysisType type : held.any()) {
            if (mayBeArray(type)) {
                return true;
            }
        }
        for (Source source : held.stored()) {
            if (source.filters().stream().allMatch(FlowReader::mayBeArray)) {
                return true;
            }
        }
        return false;
    }

    /** Whether an array can have the type: an array type, or one of the interfaces all arrays have. */
    static boolean mayBeArray(AnalysisType type) {
        if (type.isArray() || type.isJavaLangObject()) {
            return true;
        }
        String name = type.toJavaName(true);
        return name.equals("java.lang.Cloneable") || name.equals("java.io.Serializable");
    }

    /** What a flow may hold; nothing for a primitive flow or a disabled one (code the analysis never reached). */
    Held held(TypeFlow<?> flow) {
        return held(flow, false);
    }

    /**
     * What a flow may hold. {@code deferred} lets a saturated load resolve what it loads from the
     * stores into its source, once all stores are known.
     */
    Held held(TypeFlow<?> flow, boolean deferred) {
        if (flow == null || flow.isPrimitiveFlow()) {
            return Held.NOTHING;
        }
        if (flow.isSaturated() && deferred && !readFlows) {
            if (flow instanceof OffsetLoadTypeFlow.LoadIndexedTypeFlow && bb.analysisPolicy().aliasArrayTypeFlows()) {
                return new Held(List.of(), List.of(), List.of(new Source(ARRAYS, filterOf(flow))));
            } else if (flow instanceof LoadFieldTypeFlow load && !load.field().isStatic()) {
                return new Held(List.of(), List.of(), List.of(new Source(load.field(), filterOf(flow))));
            } else if (bb.trackTypeFlowInputs()) {
                return new Held(List.of(), List.of(), List.of(new Source(flow, filterOf(flow))));
            }
        }
        if (flow.isSaturated()) {
            AnalysisType declared = flow.getDeclaredType();
            return new Held(List.of(), List.of(declared != null && !declared.isPrimitive() ? declared : objectType));
        }
        TypeState state = flow.getOutputState(bb);
        if (state == null || state.isPrimitive() || state.isEmpty()) {
            return Held.NOTHING;
        }
        return filtered(new Held(List.of(state), List.of()), filterOf(flow));
    }

    /**
     * Rebuilds what a saturated flow holds from the flows that feed it: exact inputs as they are,
     * field loads by what was stored into the field, injected values as any object of the declared
     * type, and unknown inputs likewise. Needs {@code -H:+TrackInputFlows}.
     */
    Held rebuild(TypeFlow<?> start) {
        return rebuilt.computeIfAbsent(start, this::rebuildFrom);
    }

    private Held rebuildFrom(TypeFlow<?> start) {
        Set<TypeFlow<?>> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        Deque<TypeFlow<?>> queue = new ArrayDeque<>(List.of(start));
        List<TypeState> states = new ArrayList<>();
        List<AnalysisObject> kept = new ArrayList<>();
        Set<AnalysisType> any = new HashSet<>();
        Set<Source> stored = new HashSet<>();
        boolean entryPoints = assumptions.contains("entry-points") && bb.trackTypeFlowInputs();
        Map<TypeFlow<?>, TypeFlow<?>> parents = explain == null ? null : new IdentityHashMap<>();
        while (!queue.isEmpty()) {
            TypeFlow<?> flow = queue.poll();
            if (!seen.add(flow) || flow.isPrimitiveFlow() || !flow.isFlowEnabled() || escape.inVirtualMachine(flow)) {
                continue;
            }
            if (!flow.isSaturated()) {
                if (entryPoints && bb.getRootParameterFlows().contains(flow)) {
                    // What callers outside the analyzed code pass is not stored by the code; only its own calls count.
                    for (TypeFlow<?> input : flow.getInputs()) {
                        if (!input.isAllInstantiated()) {
                            queue.add(input);
                        }
                    }
                    continue;
                }
                TypeState state = flow.getOutputState(bb);
                if (state != null && !state.isPrimitive() && !state.isEmpty()) {
                    keepExact(flow, state, states, kept);
                    if (explain != null) {
                        traceFound(start, flow, state, parents);
                    }
                }
                continue;
            }
            // A saturated flow: what it reads from, or what feeds it.
            AnalysisType declared = flow.getDeclaredType() != null && !flow.getDeclaredType().isPrimitive() ? flow.getDeclaredType() : objectType;
            Collection<TypeFlow<?>> inputs = flow.getInputs();
            if (flow instanceof OffsetLoadTypeFlow.LoadIndexedTypeFlow && bb.analysisPolicy().aliasArrayTypeFlows()) {
                stored.add(new Source(ARRAYS, filterOf(flow)));
            } else if (flow instanceof LoadFieldTypeFlow load && !load.field().isStatic()) {
                stored.add(new Source(load.field(), filterOf(flow)));
            } else if (flow instanceof LoadFieldTypeFlow) {
                // A static field holds what was stored into it, which every thread can reach.
                continue;
            } else if (flow.isAllInstantiated() || inputs.isEmpty()) {
                any.add(declared);
                if (explain != null && anyPrinted++ < 400) {
                    traceAny(start, flow, declared, parents);
                }
            } else {
                boolean injected = entryPoints && bb.getRootParameterFlows().contains(flow);
                for (TypeFlow<?> input : inputs) {
                    if (injected && input.isAllInstantiated()) {
                        continue;
                    }
                    queue.add(input);
                    if (parents != null) {
                        parents.putIfAbsent(input, flow);
                    }
                }
            }
        }
        return new Held(states, new ArrayList<>(any), new ArrayList<>(stored), kept);
    }

    /** Takes what an exact flow holds: its whole state, or the objects of its declared type. */
    private void keepExact(TypeFlow<?> flow, TypeState state, List<TypeState> states, List<AnalysisObject> kept) {
        List<AnalysisType> restriction = filterOf(flow);
        if (restriction.isEmpty()) {
            states.add(state);
        } else {
            for (AnalysisObject object : state.objects(bb)) {
                if (matches(restriction, object.type())) {
                    kept.add(object);
                }
            }
        }
    }

    /** When explaining: prints how rebuilding reached each matching summary that is not shared yet. */
    private void traceFound(TypeFlow<?> start, TypeFlow<?> flow, TypeState state, Map<TypeFlow<?>, TypeFlow<?>> parents) {
        for (AnalysisObject object : state.objects(bb)) {
            if (object.isContextInsensitiveObject() && explain.matcher(GraphExport.PointsTo.objectName(object)).find() && !shared.contains(object)) {
                StringBuilder trace = new StringBuilder("THREADESCAPE rebuilding " + why.describeStored(start) + " finds " + GraphExport.PointsTo.objectName(object) + " in");
                for (TypeFlow<?> at = flow; at != null; at = parents.get(at)) {
                    trace.append("\n    ").append(why.describeStored(at)).append(at.isSaturated() ? " (saturated)" : "").append(" with ").append(at.isSaturated() ? 0
                                    : at.getOutputState(bb).typesCount()).append(" types");
                }
                PointsToExport.diagnostics().println(trace);
            }
        }
    }

    /** When explaining: prints how rebuilding reached a flow that can only say "any object of its type". */
    private void traceAny(TypeFlow<?> start, TypeFlow<?> flow, AnalysisType declared, Map<TypeFlow<?>, TypeFlow<?>> parents) {
        StringBuilder trace = new StringBuilder("THREADESCAPE rebuilding " + why.describeStored(start) + " has any " + declared.toJavaName() + " from " + why.describeStored(flow) +
                        (flow.isAllInstantiated() ? " (all instantiated)" : " (no inputs)"));
        for (TypeFlow<?> at = parents.get(flow); at != null && trace.length() < 1500; at = parents.get(at)) {
            trace.append("\n    <- ").append(why.describeStored(at)).append(at.isSaturated() ? " (saturated)" : "");
        }
        PointsToExport.diagnostics().println(trace);
    }

    /** Adds what a flow may hold; nothing for a saturated one (the caller handles it) or a disabled one. */
    void collect(TypeFlow<?> flow, Set<AnalysisObject> into) {
        TypeState state = flow.isSaturated() ? null : flow.getOutputState(bb);
        if (state != null && !state.isPrimitive()) {
            for (AnalysisObject object : state.objects(bb)) {
                into.add(object);
            }
        }
    }
}
