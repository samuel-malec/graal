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
 * What a flow of the points-to analysis may hold, in a form that survives saturation. A flow that did
 * not saturate holds the objects of its state, restricted to its declared type. A flow that did has
 * stopped saying: what it held is rebuilt from the flows that feed it (the analysis must have recorded
 * them, {@code -H:+TrackInputFlows}), where they are exact; from what was stored into the field or the
 * arrays it loads from; and where nothing is known, as any object of its type.
 */
final class FlowReader {

    /** What flows may hold: the objects the analysis knows, and any object of a type for a flow that saturated. */
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

        /** The objects the states and the list name. */
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
     * What a load that saturated reads: what was stored into a place, which is a field, the
     * arrays, or what feeds a flow, restricted to the objects that have all of the types the
     * loads on the way give.
     */
    record Source(Object key, List<AnalysisType> filters) {
    }

    private record Pair(List<AnalysisType> a, List<AnalysisType> b) {
    }

    static final class StreamSupportHelper {
        static boolean hasArray(Iterable<AnalysisObject> objects) {
            for (AnalysisObject object : objects) {
                if (object.type().isArray()) {
                    return true;
                }
            }
            return false;
        }
    }

    private final ThreadEscape escape;
    private final PointsToAnalysis bb;
    private final Set<String> assumptions;
    private final boolean readFlows;
    private final AnalysisType objectType;
    private final Pattern explain;
    private final Set<AnalysisObject> known;
    private final Set<AnalysisObject> shared;
    SharingExplanation why;

    /**
     * What a saturated flow that loads from a field, or from an array, holds: not any object of its
     * declared type, but any object stored into that field, or into any array, since the arrays
     * have one elements flow. Known when every site is.
     */
    static final Object ARRAYS = new Object();

    /** Stands for "no object has them all" in the cache of meets; a list of its own, which no meet is. */
    private static final List<AnalysisType> NOBODY = Collections.unmodifiableList(new ArrayList<>());

    final Map<Pair, List<AnalysisType>> meets = new HashMap<>();
    static final List<AnalysisType> NO_TYPES = List.of();
    private final Map<Long, Boolean> assignable = new HashMap<>();
    private final Map<AnalysisType, Set<AnalysisType>> subtypes = new HashMap<>();

    /**
     * What a flow that saturated holds, from the flows that feed it: where they are exact, what they
     * hold; where one loads from a field, what is stored into the field; where it was injected,
     * any object of its declared type; or where nothing is known about what feeds it. The analysis
     * recorded the inputs of its flows if {@code -H:+TrackInputFlows} was given.
     */
    private int anyPrinted;

    private final Map<TypeFlow<?>, Held> rebuilt = new IdentityHashMap<>();

    FlowReader(ThreadEscape escape) {
        this.escape = escape;
        this.bb = escape.bb;
        this.assumptions = escape.assumptions;
        this.readFlows = escape.readFlows;
        this.objectType = escape.objectType;
        this.explain = escape.explain;
        this.known = escape.known;
        this.shared = escape.shared;
    }

    void connect(SharingExplanation why) {
        this.why = why;
    }

    /** The same place, for a load that gives these types too; null if no object has them all. */
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

    /** The types an object must have to have all of both; null if no object can. Redundant types are left out. */
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

    static boolean noObjectHasBoth(AnalysisType x, AnalysisType y) {
        if (x.isAssignableFrom(y) || y.isAssignableFrom(x)) {
            return false;
        }
        if (!x.isInterface() && !y.isInterface()) {
            return true;
        }
        // An array has the types of arrays, and no other interface.
        AnalysisType other = x.isInterface() ? x : y;
        AnalysisType notInterface = x.isInterface() ? y : x;
        return notInterface.isArray() && !mayBeArray(other);
    }

    /**
     * The flow an access observes. When that flow saturated, the analysis has the access observe the
     * flow of the declared type instead; the one it observed first, if there was only one, says
     * more (the inputs of the flows must have been recorded).
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

    /** The types that restrict what a flow holds: its declared one, unless that says nothing. */
    private List<AnalysisType> filterOf(TypeFlow<?> flow) {
        AnalysisType declared = flow.getDeclaredType();
        return declared == null || declared.isPrimitive() || declared.isJavaLangObject() ? NO_TYPES : List.of(declared);
    }

    boolean assignableTo(AnalysisType filter, AnalysisType type) {
        long key = filter.getId() * 0x9E3779B97F4A7C15L + type.getId();
        Boolean known = assignable.get(key);
        if (known == null) {
            known = filter.isAssignableFrom(type);
            assignable.put(key, known);
        }
        return known;
    }

    boolean matches(List<AnalysisType> filters, AnalysisType type) {
        for (AnalysisType filter : filters) {
            if (!assignableTo(filter, type)) {
                return false;
            }
        }
        return true;
    }

    /** The type and all its subtypes, which the hierarchy lists; arrays are not among them. */
    Set<AnalysisType> subtypesOf(AnalysisType type) {
        Set<AnalysisType> found = subtypes.get(type);
        if (found == null) {
            found = new HashSet<>();
            type.getAllSubtypes().forEach(found::add);
            subtypes.put(type, found);
        }
        return found;
    }

    /** What a held holds of the types: the objects that have them, the types it narrows to, and where else it reads from, narrowed. */
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
        for (AnalysisType type : held.any()) {
            if (matches(filters, type)) {
                any.add(type);
                continue;
            }
            boolean added = false;
            boolean unrelated = false;
            for (AnalysisType filter : filters) {
                if (type.isAssignableFrom(filter)) {
                    any.add(filter);
                    added = true;
                } else if (!filter.isAssignableFrom(type) && !noObjectHasBoth(type, filter)) {
                    unrelated = true;
                }
            }
            if (!added && unrelated) {
                any.add(type);
            }
        }
        List<Source> stored = new ArrayList<>();
        for (Source source : held.stored()) {
            Source narrowed = narrowed(source, filters);
            if (narrowed != null) {
                stored.add(narrowed);
            }
        }
        return new Held(List.of(), any, stored, objects);
    }

    /** Whether the objects may include an array: one that is, or a flow that saturated at a type an array may have. */
    boolean mayBeArray(Held held) {
        if (StreamSupportHelper.hasArray(held.objectsIn(bb))) {
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

    /** Whether an array can have the type: an array type, or one of the types all arrays have. */
    static boolean mayBeArray(AnalysisType type) {
        if (type.isArray() || type.isJavaLangObject()) {
            return true;
        }
        String name = type.toJavaName(true);
        return name.equals("java.lang.Cloneable") || name.equals("java.io.Serializable");
    }

    /** What a flow may hold: nothing for a flow of primitives or one that is disabled, in code the analysis never reached. */
    Held held(TypeFlow<?> flow) {
        return held(flow, false);
    }

    /**
     * What a flow may hold. {@code deferred} lets a saturated load say what it loads from the stores
     * into what it loads from, once they are all known.
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
                    // What the callers outside the analysed code pass is not what the code stores: only the calls it makes.
                    for (TypeFlow<?> input : flow.getInputs()) {
                        if (!input.isAllInstantiated()) {
                            queue.add(input);
                        }
                    }
                    continue;
                }
                TypeState state = flow.getOutputState(bb);
                if (state != null && !state.isPrimitive() && !state.isEmpty()) {
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
                    if (explain != null) {
                        for (AnalysisObject object : state.objects(bb)) {
                            if (object.isContextInsensitiveObject() && explain.matcher(GraphExport.PointsTo.objectName(object)).find() && !shared.contains(object)) {
                                StringBuilder trace = new StringBuilder("THREADESCAPE rebuilding " + why.describeStored(start) + " finds " + GraphExport.PointsTo.objectName(object) + " in");
                                for (TypeFlow<?> at = flow; at != null; at = parents.get(at)) {
                                    trace.append("\n    ").append(why.describeStored(at)).append(at.isSaturated() ? " (saturated)" : "").append(" with ").append(at.isSaturated() ? 0 : at.getOutputState(bb).typesCount()).append(" types");
                                }
                                System.err.println(trace);
                            }
                        }
                    }
                }
                continue;
            }
            AnalysisType declared = flow.getDeclaredType() != null && !flow.getDeclaredType().isPrimitive() ? flow.getDeclaredType() : objectType;
            Collection<TypeFlow<?>> inputs = flow.getInputs();
            if (flow instanceof OffsetLoadTypeFlow.LoadIndexedTypeFlow && bb.analysisPolicy().aliasArrayTypeFlows()) {
                stored.add(new Source(ARRAYS, filterOf(flow)));
            } else if (flow instanceof LoadFieldTypeFlow load && !load.field().isStatic()) {
                stored.add(new Source(load.field(), filterOf(flow)));
            } else if (flow instanceof LoadFieldTypeFlow) {
                // A static field holds what was stored into it, which every thread reaches.
                continue;
            } else if (flow.isAllInstantiated() || inputs.isEmpty()) {
                any.add(declared);
                if (explain != null && anyPrinted++ < 400) {
                    StringBuilder trace = new StringBuilder("THREADESCAPE rebuilding " + why.describeStored(start) + " has any " + declared.toJavaName() + " from " + why.describeStored(flow) +
                                    (flow.isAllInstantiated() ? " (all instantiated)" : " (no inputs)"));
                    for (TypeFlow<?> at = parents.get(flow); at != null && trace.length() < 1500; at = parents.get(at)) {
                        trace.append("\n    <- ").append(why.describeStored(at)).append(at.isSaturated() ? " (saturated)" : "");
                    }
                    System.err.println(trace);
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

    /** Adds what a flow may hold: nothing for a saturated one, which its caller handles, or a disabled one, in code the analysis never reached. */
    void collect(TypeFlow<?> flow, Set<AnalysisObject> into) {
        TypeState state = flow.isSaturated() ? null : flow.getOutputState(bb);
        if (state != null && !state.isPrimitive()) {
            for (AnalysisObject object : state.objects(bb)) {
                into.add(object);
            }
        }
    }
}
