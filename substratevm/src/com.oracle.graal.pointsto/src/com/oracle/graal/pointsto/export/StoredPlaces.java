package com.oracle.graal.pointsto.export;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.export.FlowReader.Held;
import com.oracle.graal.pointsto.export.FlowReader.Source;
import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.flow.context.object.AnalysisObject;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisType;

/**
 * What was stored into the places a saturated load reads from: a field, all the arrays (the analysis gives
 * them one elements flow), or a flow that is rebuilt from its inputs. Finds, once for each place, everything
 * that may be in it and in the places it loads from (a closure, found with Tarjan's algorithm so that places
 * on a cycle share one), restricts it to the types a load asks for when it is read, and shares what a place
 * holds.
 */
final class StoredPlaces {

    /** What is stored into one place: the objects by exact type, the types of saturated stores, and the places it loads from. */
    private static final class PlaceData {
        final Map<AnalysisType, List<AnalysisObject>> byType = new HashMap<>();
        final List<AnalysisType> arrayTypes = new ArrayList<>();
        final Set<AnalysisType> any = new LinkedHashSet<>();
        final Set<Source> nested = new LinkedHashSet<>();
    }

    /** What a place holds, with the places it loads from, transitively, of all types: found once for a place, restricted for each load. */
    private static final class Closure {
        final Set<AnalysisObject> objects = new LinkedHashSet<>();
        final Set<AnalysisType> any = new LinkedHashSet<>();
        /** Too many objects to name: any object of any type. */
        boolean tooMany;
    }

    private final ThreadEscape escape;
    private final PointsToAnalysis bb;
    private final AnalysisType objectType;
    private final Pattern explain;
    private final Set<AnalysisObject> shared;
    FlowReader reader;
    SharingExplanation why;

    final Map<AnalysisField, List<Held>> storedInField = new HashMap<>();
    final List<Held> storedInArrays = new ArrayList<>();
    final List<Held> storedUnsafely = new ArrayList<>();
    private final Set<Source> storedShared = new HashSet<>();
    private final Set<Source> storedContentsShared = new HashSet<>();

    /** For each place, the types of what was shared of it, so that what a weaker restriction shared is not shared again. */
    private final Map<Integer, Map<Object, List<List<AnalysisType>>>> doneByKey = new HashMap<>();

    /** For the explanation: the place being read, and which place it was reached from. */
    Source currentSource;

    final Map<Source, Source> sourceParent = new HashMap<>();
    final Map<Object, PlaceData> placeTable = new HashMap<>();

    /**
     * More objects than this in what a place holds, and it is taken as any object of the types
     * asked for: it has stopped telling objects apart.
     */
    private static final int MOST_OBJECTS = Integer.getInteger("sideeffects.mostObjects", 20_000);

    long visits;
    long childrenSeen;
    long shareVisits;
    final Map<Object, Closure> closures = new HashMap<>();

    StoredPlaces(ThreadEscape escape) {
        this.escape = escape;
        this.bb = escape.bb;
        this.objectType = escape.objectType;
        this.explain = escape.explain;
        this.shared = escape.shared;
    }

    void connect(FlowReader reader, SharingExplanation why) {
        this.reader = reader;
        this.why = why;
    }

    /** Shares what was stored into a place, of the types asked for, and what is stored into the places it loads from. */
    void shareSource(Source start, boolean contentsOnly) {
        Deque<Source> queue = new ArrayDeque<>();
        queue.add(start);
        Set<Source> done = contentsOnly ? storedContentsShared : storedShared;
        while (!queue.isEmpty()) {
            Source at = queue.poll();
            if (ThreadEscape.PROGRESS && ++shareVisits % 100_000 == 0) {
                System.err.println("THREADPROGRESS shared places " + shareVisits + ", queue " + queue.size() + ", shared " + shared.size());
            }
            if (explain != null) {
                currentSource = at;
            }
            PlaceData data = placeData(at.key());
            ofTypes(data, at.filters(), objects -> objects.forEach(contentsOnly ? escape::shareContents : escape::share));
            Set<AnalysisType> any = new LinkedHashSet<>();
            narrowAny(any, data.any, at.filters());
            for (AnalysisType type : any) {
                if (contentsOnly) {
                    if (escape.anyContentsOf.add(type) && explain != null) {
                        why.recordAnyOf(type);
                    }
                } else {
                    escape.addAnyOf(type);
                }
            }
            for (Source nested : data.nested) {
                Source narrowed = reader.narrowed(nested, at.filters());
                if (narrowed != null && claim(narrowed, contentsOnly)) {
                    if (explain != null) {
                        sourceParent.put(narrowed, at);
                    }
                    queue.add(narrowed);
                }
            }
        }
    }

    /** Takes a place to share what it holds of the types; false if that, or more, was taken already. */
    boolean claim(Source source, boolean contentsOnly) {
        Set<Source> done = contentsOnly ? storedContentsShared : storedShared;
        Map<Object, List<List<AnalysisType>>> byKey = doneByKey.computeIfAbsent(contentsOnly ? 1 : 0, k -> new HashMap<>());
        List<List<AnalysisType>> taken = byKey.computeIfAbsent(source.key(), k -> new ArrayList<>());
        for (List<AnalysisType> weaker : taken) {
            if (weaker.isEmpty() || weaker.equals(source.filters()) || allAssignable(weaker, source.filters())) {
                return false;
            }
        }
        done.add(source);
        taken.add(source.filters());
        return true;
    }

    /** Whether everything with all of the narrower types has all of the weaker ones. */
    private boolean allAssignable(List<AnalysisType> weaker, List<AnalysisType> narrower) {
        for (AnalysisType type : weaker) {
            boolean implied = false;
            for (AnalysisType other : narrower) {
                if (reader.assignableTo(type, other)) {
                    implied = true;
                    break;
                }
            }
            if (!implied) {
                return false;
            }
        }
        return true;
    }

    /** Calls the consumer with the objects of each exact type that has all the types: by the hierarchy, not by testing every type. */
    private void ofTypes(PlaceData data, List<AnalysisType> filters, java.util.function.Consumer<List<AnalysisObject>> consumer) {
        if (filters.isEmpty()) {
            data.byType.values().forEach(consumer);
            return;
        }
        AnalysisType first = filters.get(0);
        if (!first.isArray()) {
            Set<AnalysisType> below = reader.subtypesOf(first);
            Collection<AnalysisType> smaller = below.size() < data.byType.size() ? below : data.byType.keySet();
            for (AnalysisType type : smaller) {
                List<AnalysisObject> objects = data.byType.get(type);
                if (objects != null && below.contains(type) && reader.matches(filters, type)) {
                    consumer.accept(objects);
                }
            }
        }
        if (first.isArray() || FlowReader.mayBeArray(first)) {
            for (AnalysisType type : data.arrayTypes) {
                if (reader.matches(filters, type)) {
                    consumer.accept(data.byType.get(type));
                }
            }
        }
    }

    /** What is stored into a place: the objects by exact type, the types of saturated stores, and the places it loads from. */
    private PlaceData placeData(Object key) {
        PlaceData data = placeTable.get(key);
        if (data == null) {
            data = new PlaceData();
            Map<AnalysisType, Set<AnalysisObject>> unique = new HashMap<>();
            for (Held held : storedIn(key)) {
                for (AnalysisObject object : held.objectsIn(bb)) {
                    unique.computeIfAbsent(object.type(), k -> new LinkedHashSet<>()).add(object);
                }
                data.any.addAll(held.any());
                data.nested.addAll(held.stored());
            }
            for (Map.Entry<AnalysisType, Set<AnalysisObject>> entry : unique.entrySet()) {
                data.byType.put(entry.getKey(), new ArrayList<>(entry.getValue()));
                if (entry.getKey().isArray()) {
                    data.arrayTypes.add(entry.getKey());
                }
            }
            placeTable.put(key, data);
        }
        return data;
    }

    /** Adds the types of a saturated store that can be of the types asked for: the types themselves, or the types asked for that they stand for. */
    private void narrowAny(Set<AnalysisType> into, Iterable<AnalysisType> any, List<AnalysisType> filters) {
        for (AnalysisType type : any) {
            if (reader.matches(filters, type)) {
                into.add(type);
                continue;
            }
            boolean added = false;
            boolean unrelated = false;
            for (AnalysisType filter : filters) {
                if (type.isAssignableFrom(filter)) {
                    into.add(filter);
                    added = true;
                } else if (!filter.isAssignableFrom(type) && !FlowReader.noObjectHasBoth(type, filter)) {
                    unrelated = true;
                }
            }
            if (!added && unrelated) {
                into.add(type);
            }
        }
    }

    /** What is stored into the field, or into any array, as far as the sites say, or what feeds a flow that saturated. */
    private List<Held> storedIn(Object where) {
        if (where == FlowReader.ARRAYS) {
            return storedInArrays;
        }
        if (where instanceof TypeFlow<?> flow) {
            return List.of(reader.rebuild(flow));
        }
        AnalysisField field = (AnalysisField) where;
        List<Held> values = new ArrayList<>(storedInField.getOrDefault(field, List.of()));
        if (field.isUnsafeAccessed()) {
            values.addAll(storedUnsafely);
        }
        return values;
    }

    /** What a held may hold once every store is known: its own, and the stores into what it loads from, transitively. */
    Held expand(Held held) {
        if (held.stored().isEmpty()) {
            return held;
        }
        Set<AnalysisObject> objects = new LinkedHashSet<>();
        held.objectsIn(bb).forEach(objects::add);
        Set<AnalysisType> any = new LinkedHashSet<>(held.any());
        for (Source source : held.stored()) {
            restrict(closureOf(source.key()), source.filters(), objects, any);
        }
        return new Held(List.of(), new ArrayList<>(any), List.of(), new ArrayList<>(objects));
    }

    /** Adds what a closure holds of the types, to the objects and the types of a held. */
    private void restrict(Closure closure, List<AnalysisType> filters, Set<AnalysisObject> objects, Set<AnalysisType> any) {
        if (closure.tooMany) {
            narrowAny(any, List.of(objectType), filters);
            return;
        }
        if (filters.isEmpty()) {
            objects.addAll(closure.objects);
            any.addAll(closure.any);
            return;
        }
        for (AnalysisObject object : closure.objects) {
            if (reader.matches(filters, object.type())) {
                objects.add(object);
            }
        }
        narrowAny(any, closure.any, filters);
    }

    /** The closure of a place, found with Tarjan's algorithm so that every place on a cycle gets the same one, and none is found twice. */
    private Closure closureOf(Object start) {
        Closure done = closures.get(start);
        if (done != null) {
            return done;
        }
        Map<Object, Integer> index = new HashMap<>();
        Map<Object, Integer> low = new HashMap<>();
        Map<Object, List<Source>> kids = new HashMap<>();
        Deque<Object> stack = new ArrayDeque<>();
        Set<Object> onStack = new HashSet<>();
        Deque<Object> frames = new ArrayDeque<>();
        Map<Object, Iterator<Source>> next = new HashMap<>();
        int[] counter = {0};
        java.util.function.Consumer<Object> visit = node -> {
            visits++;
            index.put(node, counter[0]);
            low.put(node, counter[0]);
            counter[0]++;
            stack.push(node);
            onStack.add(node);
            List<Source> children = new ArrayList<>(placeData(node).nested);
            childrenSeen += children.size();
            kids.put(node, children);
            next.put(node, children.iterator());
            frames.push(node);
        };
        visit.accept(start);
        while (!frames.isEmpty()) {
            Object node = frames.peek();
            Iterator<Source> children = next.get(node);
            if (children.hasNext()) {
                Object child = children.next().key();
                if (closures.containsKey(child)) {
                    continue;
                }
                if (!index.containsKey(child)) {
                    visit.accept(child);
                } else if (onStack.contains(child)) {
                    low.put(node, Math.min(low.get(node), index.get(child)));
                }
            } else {
                frames.pop();
                if (!frames.isEmpty()) {
                    Object parent = frames.peek();
                    low.put(parent, Math.min(low.get(parent), low.get(node)));
                }
                if (low.get(node).equals(index.get(node))) {
                    List<Object> members = new ArrayList<>();
                    Object member;
                    do {
                        member = stack.pop();
                        onStack.remove(member);
                        members.add(member);
                    } while (member != node);
                    Closure closure = new Closure();
                    Set<Object> inside = new HashSet<>(members);
                    for (Object m : members) {
                        PlaceData data = placeData(m);
                        if (!closure.tooMany) {
                            int[] count = {0};
                            ofTypes(data, FlowReader.NO_TYPES, found -> count[0] += found.size());
                            if (closure.objects.size() + count[0] > MOST_OBJECTS) {
                                closure.tooMany = true;
                            } else {
                                ofTypes(data, FlowReader.NO_TYPES, found -> closure.objects.addAll(found));
                            }
                        }
                        closure.any.addAll(data.any);
                        for (Source edge : kids.get(m)) {
                            Object child = edge.key();
                            if (inside.contains(child)) {
                                continue;
                            }
                            Closure finished = closures.get(child);
                            if (closure.tooMany) {
                                break;
                            }
                            restrict(finished, edge.filters(), closure.objects, closure.any);
                            if (closure.objects.size() > MOST_OBJECTS) {
                                closure.tooMany = true;
                            }
                        }
                    }
                    if (closure.tooMany) {
                        closure.objects.clear();
                        closure.any.clear();
                        closure.any.add(objectType);
                    }
                    for (Object m : members) {
                        closures.put(m, closure);
                    }
                }
            }
        }
        return closures.get(start);
    }
}
