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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.graalvm.word.LocationIdentity;

import com.oracle.graal.pointsto.export.PointsToExport;
import com.oracle.svm.core.graal.snippets.SubstrateAllocationSnippets;
import com.oracle.svm.core.thread.SafepointCheckCounter;
import com.oracle.svm.hosted.meta.HostedField;
import com.oracle.svm.hosted.meta.HostedMethod;
import com.oracle.svm.hosted.meta.HostedUniverse;

import jdk.graal.compiler.nodes.FieldLocationIdentity;
import jdk.graal.compiler.nodes.NamedLocationIdentity;
import jdk.graal.compiler.nodes.java.MethodCallTargetNode;
import jdk.vm.ci.meta.JavaKind;

/**
 * Turns kills.txt (what each method may write, including through its callees) into Graal locations.
 * A call kills the union of what its possible callees may write.
 * <p>
 * Every narrowed call also kills the VM state that a safepoint in a callee may change, as Native
 * Image's own safepoints do; see {@link SideEffectAnalysisFeature}.
 */
final class KillSets {
    private final String program;
    private final boolean vm;
    private final boolean platform;
    /** Method name and descriptor to the partitions it may write; a missing method may write anything. */
    private final Map<String, List<String>> written = new HashMap<>();
    /** The image's fields by name, to build Graal locations for partitions. */
    private final Map<String, HostedField> fields = new HashMap<>();
    /** The VM state every narrowed call kills. */
    private final List<LocationIdentity> vmState = new ArrayList<>();
    /** Number of lines in kills.txt, for timings.txt. */
    private long methodsWithFacts;
    /**
     * Upper bound, never sound: every call kills only {@link #killedByEveryCall()}, whatever its
     * callees write.
     */
    private boolean writeNothing;

    /**
     * @param vm whether narrowed calls kill the VM state and the VM locations a callee writes (off
     *            only for testing)
     * @param platform whether calls kill the JDK and VM fields their callees write (off only for
     *            testing)
     */
    KillSets(String program, boolean vm, boolean platform) {
        this.program = program;
        this.vm = vm;
        this.platform = platform;
    }

    /** Reads kills.txt: per line the method, a tab, and its partitions or {@code any}. */
    void read(List<String> kills) {
        for (String line : kills) {
            methodsWithFacts++;
            String[] parts = line.split("\t", -1);
            if (!parts[1].equals("any")) {
                written.put(parts[0], parts[1].isEmpty() ? List.of() : List.of(parts[1].split(",")));
            }
        }
    }

    /**
     * Upper bound for a measurement, never sound: no call writes a field or an array, only the VM's
     * state that every narrowed call kills stays. Counts what the kill sets could free at most, and
     * needs no facts and no list of kill sets. The image may be wrong and must not be run.
     */
    void writeNothing() {
        writeNothing = true;
    }

    /** Test only: claims that a method writes nothing, so a wrong answer shows in the program's output. */
    void claimWritesNothing(String method) {
        written.put(method, List.of());
    }

    /** Number of methods in kills.txt, {@code any} included. */
    long methodsWithFacts() {
        return methodsWithFacts;
    }

    /** Looks up the image's fields (Graal locations are built from them) and collects the VM state. */
    void useImage(HostedUniverse universe) {
        for (HostedField field : universe.getFields()) {
            fields.put(Names.fieldName(field), field);
        }
        // What Native Image's safepoint kills (SafepointSnippets).
        vmState.addAll(List.of(SubstrateAllocationSnippets.GC_LOCATIONS));
        vmState.add(SafepointCheckCounter.getLocationIdentity());
        HostedField sessionState = fields.get("jdk.internal.foreign.MemorySessionImpl.state");
        if (sessionState != null) {
            vmState.add(new FieldLocationIdentity(sessionState));
        }
    }

    /** What every narrowed call kills in addition to its callees' writes: the VM state (unless disabled for testing). */
    List<LocationIdentity> killedByEveryCall() {
        return vm ? vmState : List.of();
    }

    /** Whether a location is part of the VM state every narrowed call kills. */
    boolean isVMState(LocationIdentity location) {
        return vmState.contains(location);
    }

    /**
     * What a call may write: the union of the kill sets of all its possible targets, or null for
     * anything. A field in {@code partitioned} is killed both as a whole and in its partition.
     */
    LocationIdentity[] killsOf(MethodCallTargetNode target, Set<String> partitioned) {
        if (writeNothing) {
            return new LocationIdentity[0];
        }
        HostedMethod method = (HostedMethod) target.targetMethod();
        HostedMethod[] callees = target.invokeKind().isDirect() ? new HostedMethod[]{method} : method.getImplementations();
        if (callees.length == 0) {
            return null;
        }
        List<LocationIdentity> all = new ArrayList<>();
        for (HostedMethod callee : callees) {
            List<String> partitions = written.get(Names.exportName(callee));
            if (partitions == null) {
                return null;
            }
            for (String partitionWritten : partitions) {
                List<LocationIdentity> locations = locations(partitionWritten, partitioned);
                if (locations == null) {
                    return null;
                }
                all.addAll(locations);
            }
        }
        return all.toArray(new LocationIdentity[0]);
    }

    /**
     * The Graal locations for a name in kills.txt: a field, an array kind, or (with object-field
     * partitions) a field in one group of objects, e.g. {@code Aliasing$Counter.value@main:199}. A
     * field that is partitioned in this graph is killed in its partition and also as a whole, because
     * some phases (read elimination) key field accesses by the field alone. Other fields are killed
     * whole.
     */
    private List<LocationIdentity> locations(String partition, Set<String> partitioned) {
        if (partition.equals("init")) {
            return List.of(); // the callee initializes what it allocates itself; see SideEffectAnalysisFeature
        }
        if (partition.startsWith("vm:")) {
            LocationIdentity location = PointsToExport.VM_LOCATIONS.get(partition);
            return !vm ? List.of() : location != null ? List.of(location) : null; // null: not a VM location known to this build, so anything
        }
        String whole = partition.contains("@") ? partition.substring(0, partition.indexOf('@')) : partition;
        if (whole.endsWith("[]")) {
            return arrayKinds(whole).stream().map(NamedLocationIdentity::getArrayLocation).toList();
        }
        HostedField field = fields.get(whole);
        if (field == null || (!platform && !PointsToExport.isProgramClass(field.getDeclaringClass().toJavaName(true), program))) {
            return List.of(); // not accessed in the image, so nothing to kill (or the platform-field kill is disabled for testing)
        }
        return partitioned.contains(whole) ? List.of(new FieldLocationIdentity(field), new FieldLocationIdentity(field, false, partition))
                        : List.of(new FieldLocationIdentity(field));
    }

    /** The element kinds of an array partition name; {@code byte[]} also stands for {@code boolean[]}. */
    private static List<JavaKind> arrayKinds(String partition) {
        return switch (partition) {
            case "byte[]" -> List.of(JavaKind.Byte, JavaKind.Boolean);
            case "Object[]" -> List.of(JavaKind.Object);
            default -> List.of(JavaKind.fromJavaClass(primitive(partition.substring(0, partition.length() - 2))));
        };
    }

    /** The class of a primitive type, by name. */
    private static Class<?> primitive(String name) {
        return switch (name) {
            case "char" -> char.class;
            case "short" -> short.class;
            case "int" -> int.class;
            case "long" -> long.class;
            case "float" -> float.class;
            case "double" -> double.class;
            default -> throw new IllegalArgumentException("Not an array kind: " + name);
        };
    }
}
