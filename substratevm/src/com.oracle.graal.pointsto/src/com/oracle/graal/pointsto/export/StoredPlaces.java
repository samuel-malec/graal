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
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.regex.Pattern;

import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.export.FlowReader.Held;
import com.oracle.graal.pointsto.export.FlowReader.Source;
import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.flow.context.object.AnalysisObject;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisType;

/**
 * Tracks what was stored into the places a saturated load reads from: a field, all arrays (the
 * analysis gives them one element flow), or a flow rebuilt from its inputs. For each place it
 * computes, once, everything that may be in it and in the places it loads from (a transitive
 * closure, using Tarjan's algorithm so places on a cycle share one result), restricts that to the
 * types a load asks for, and shares it.
 */
final class StoredPlaces {

    /** What is stored into one place: objects by exact type, types of saturated stores, and the places it loads from. */
    private static final class PlaceData {
        final Map<AnalysisType, List<AnalysisObject>> byType = new HashMap<>();
        final List<AnalysisType> arrayTypes = new ArrayList<>();
        final Set<AnalysisType> any = new LinkedHashSet<>();
        final Set<Source> nested = new LinkedHashSet<>();
    }

    /** Everything a place holds, including transitively through places it loads from; computed once per place, restricted per load. */
    private static final class Closure {
        final Set<AnalysisObject> objects = new LinkedHashSet<>();
        final Set<AnalysisType> any = new LinkedHashSet<>();
        /** Too many objects to track: any object of any type. */
        boolean tooMany;
    }

    /** Above this many objects, a place counts as holding any object of the requested types. */
    private static final int MOST_OBJECTS = Integer.getInteger("sideeffects.mostObjects", 20_000);

    // Shared with the thread-escape run these places belong to.
    private final ThreadEscape escape;
    private final PointsToAnalysis bb;
    private final AnalysisType objectType;
    private final Pattern explain;
    private final Set<AnalysisObject> shared;
    FlowReader reader;
    SharingExplanation why;

    /** What the sites store: per field, into any array, and by unsafe stores (which may target an unsafe-accessed field). */
    final Map<AnalysisField, List<Held>> storedInField = new HashMap<>();
    final List<Held> storedInArrays = new ArrayList<>();
    final List<Held> storedUnsafely = new ArrayList<>();

    /** What is stored into each place; created on first request. */
    final Map<Object, PlaceData> placeTable = new HashMap<>();

    /** Each place's closure, computed on first need, after all stores are known. */
    final Map<Object, Closure> closures = new HashMap<>();

    /**
     * Per place, the types already shared from it (as objects and as contents), so that a narrower
     * request doesn't share the same objects again.
     */
    private final Map<Object, List<List<AnalysisType>>> taken = new HashMap<>();
    private final Map<Object, List<List<AnalysisType>>> contentsTaken = new HashMap<>();

    /** For explanations: the place being read and the place it was reached from. */
    Source currentSource;
    final Map<Source, Source> sourceParent = new HashMap<>();

    // Work counters for the progress output.
    long visits;
    long childrenSeen;
    long shareVisits;

    StoredPlaces(ThreadEscape escape) {
        this.escape = escape;
        this.bb = escape.bb;
        this.objectType = escape.objectType;
        this.explain = escape.explain;
        this.shared = escape.shared;
    }

    /** Connects the places to the other parts of thread escape, created after them. */
    void connect(FlowReader reader, SharingExplanation why) {
        this.reader = reader;
        this.why = why;
    }

    /** Shares what was stored into a place (of the requested types) and into the places it loads from. */
    void shareSource(Source start, boolean contentsOnly) {
        Deque<Source> queue = new ArrayDeque<>();
        queue.add(start);
        while (!queue.isEmpty()) {
            Source at = queue.poll();
            if (ThreadEscape.PROGRESS && ++shareVisits % 100_000 == 0) {
                PointsToExport.diagnostics().println("THREADPROGRESS shared places " + shareVisits + ", queue " + queue.size() + ", shared " + shared.size());
            }
            if (explain != null) {
                currentSource = at;
            }
            PlaceData data = placeData(at.key());
            ofTypes(data, at.filters(), objects -> objects.forEach(contentsOnly ? escape::shareContents : escape::share));
            Set<AnalysisType> any = new LinkedHashSet<>();
            reader.narrowAny(any, data.any, at.filters());
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

    /** Marks a place as shared for these types; false if these or wider types were already done. */
    boolean claim(Source source, boolean contentsOnly) {
        List<List<AnalysisType>> types = (contentsOnly ? contentsTaken : taken).computeIfAbsent(source.key(), k -> new ArrayList<>());
        for (List<AnalysisType> weaker : types) {
            if (weaker.isEmpty() || weaker.equals(source.filters()) || allAssignable(weaker, source.filters())) {
                return false;
            }
        }
        types.add(source.filters());
        return true;
    }

    /** Whether every object with all the narrower types also has all the wider ones. */
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

    /** Calls the consumer with the objects of each exact type that has all the given types, walking the type hierarchy. */
    private void ofTypes(PlaceData data, List<AnalysisType> filters, Consumer<List<AnalysisObject>> consumer) {
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

    /** What is stored into a place: objects by exact type, types of saturated stores, and the places it loads from. */
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

    /** What the sites store into the field or into any array, or what feeds a saturated flow. */
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

    /** What a value may hold once all stores are known: its own objects plus, transitively, what was stored into what it loads from. */
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

    /** Adds a closure's objects and types, restricted to the given types, to a value's contents. */
    private void restrict(Closure closure, List<AnalysisType> filters, Set<AnalysisObject> objects, Set<AnalysisType> any) {
        if (closure.tooMany) {
            reader.narrowAny(any, List.of(objectType), filters);
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
        reader.narrowAny(any, closure.any, filters);
    }

    /** Computes a place's closure with Tarjan's algorithm: places on a cycle share one closure, and none is computed twice. */
    private Closure closureOf(Object start) {
        Closure done = closures.get(start);
        if (done != null) {
            return done;
        }
        Map<Object, Integer> index = new HashMap<>(); // visit order
        Map<Object, Integer> low = new HashMap<>(); // lowest index reachable within the component
        Map<Object, List<Source>> kids = new HashMap<>(); // the places each place loads from
        Deque<Object> stack = new ArrayDeque<>(); // visited places whose component isn't finished
        Set<Object> onStack = new HashSet<>();
        Deque<Object> frames = new ArrayDeque<>(); // the current DFS path
        Map<Object, Iterator<Source>> next = new HashMap<>(); // next child to visit, per place
        int[] counter = {0};
        Consumer<Object> visit = node -> {
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
                if (low.get(node).equals(index.get(node))) { // node is the root of a finished component
                    List<Object> members = new ArrayList<>();
                    Object member;
                    do {
                        member = stack.pop();
                        onStack.remove(member);
                        members.add(member);
                    } while (member != node);
                    Closure closure = closureOfGroup(members, kids);
                    for (Object m : members) {
                        closures.put(m, closure);
                    }
                }
            }
        }
        return closures.get(start);
    }

    /**
     * The closure shared by the places of one cycle: what each holds, plus what the places outside
     * the cycle that they load from hold (already computed), restricted to the loaded types.
     */
    private Closure closureOfGroup(List<Object> members, Map<Object, List<Source>> kids) {
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
        return closure;
    }
}
