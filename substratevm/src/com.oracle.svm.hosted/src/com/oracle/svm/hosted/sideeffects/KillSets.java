package com.oracle.svm.hosted.sideeffects;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
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
 * What each method, with everything it calls, may write, as the tool says (kills.txt), in Graal's
 * locations: what a call kills is what its callees may write.
 * <p>
 * Every narrowed call also kills what a safepoint in its callees may change, as Native Image's own
 * safepoints do: see {@link SideEffectAnalysisFeature}.
 */
final class KillSets {
    private final String program;
    private final boolean vm;
    private final boolean platform;
    /**
     * Method name and descriptor -> the partitions it may write; absent: anything.
     */
    private final Map<String, List<String>> written = new HashMap<>();
    /**
     * The image's fields by name, to give Graal's locations for the partitions.
     */
    private final Map<String, HostedField> fields = new HashMap<>();
    /**
     * The VM's state every narrowed call kills.
     */
    private final List<LocationIdentity> vmState = new ArrayList<>();
    private long methodsWithFacts;

    /**
     * @param vm whether every narrowed call kills the VM's state and the VM's locations a callee
     *            writes (off is a control)
     * @param platform whether a call kills the platform's fields its callees write (off is a
     *            control)
     */
    KillSets(String program, boolean vm, boolean platform) {
        this.program = program;
        this.vm = vm;
        this.platform = platform;
    }

    /** Reads what each method may write: method, a tab, and the partitions, or any. */
    void read(Path kills) throws IOException {
        for (String line : Files.readAllLines(kills)) {
            methodsWithFacts++;
            String[] parts = line.split("\t", -1);
            if (!parts[1].equals("any")) {
                written.put(parts[0], parts[1].isEmpty() ? List.of() : List.of(parts[1].split(",")));
            }
        }
    }

    /** Control: claims that a method writes nothing, so that a wrong answer shows in the output. */
    void claimWritesNothing(String method) {
        written.put(method, List.of());
    }

    long methodsWithFacts() {
        return methodsWithFacts;
    }

    /** Takes the image's fields, which Graal's locations are made of, and the VM's state. */
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

    /** What every narrowed call kills besides what its callees write: the VM's state, unless the control leaves it out. */
    List<LocationIdentity> killedByEveryCall() {
        return vm ? vmState : List.of();
    }

    boolean isVMState(LocationIdentity location) {
        return vmState.contains(location);
    }

    /**
     * What a call may write: the kills of every method it may call, null for anything. A field
     * that {@code partitioned} names is killed in its partition too.
     */
    LocationIdentity[] killsOf(MethodCallTargetNode target, Set<String> partitioned) {
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
     * Graal's locations for a partition the tool names: a field, an array kind, or with objects
     * told apart a field of a set of them, Aliasing$Counter.value@main:199. A field this graph
     * gives partitions is killed in its partition, and as a whole too, for the phases that key
     * field accesses by the field alone, such as read elimination; any other is killed whole.
     */
    private List<LocationIdentity> locations(String partition, Set<String> partitioned) {
        if (partition.equals("init")) {
            return List.of(); // the callee's own initialization: see SideEffectAnalysisFeature
        }
        if (partition.startsWith("vm:")) {
            LocationIdentity location = PointsToExport.VM_LOCATIONS.get(partition);
            return !vm ? List.of() : location != null ? List.of(location) : null; // null: unnamed here, so anything
        }
        String whole = partition.contains("@") ? partition.substring(0, partition.indexOf('@')) : partition;
        if (whole.endsWith("[]")) {
            return arrayKinds(whole).stream().map(NamedLocationIdentity::getArrayLocation).toList();
        }
        HostedField field = fields.get(whole);
        if (field == null || (!platform && !PointsToExport.isProgramClass(field.getDeclaringClass().toJavaName(true), program))) {
            return List.of(); // the image never accesses it, so there is nothing to kill; or the control
        }
        return partitioned.contains(whole) ? List.of(new FieldLocationIdentity(field), new FieldLocationIdentity(field, false, partition))
                        : List.of(new FieldLocationIdentity(field));
    }

    /**
     * The element kinds of an export's array partition: byte[] stands for boolean[] too.
     */
    private static List<JavaKind> arrayKinds(String partition) {
        return switch (partition) {
            case "byte[]" -> List.of(JavaKind.Byte, JavaKind.Boolean);
            case "Object[]" -> List.of(JavaKind.Object);
            default -> List.of(JavaKind.fromJavaClass(primitive(partition.substring(0, partition.length() - 2))));
        };
    }

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
