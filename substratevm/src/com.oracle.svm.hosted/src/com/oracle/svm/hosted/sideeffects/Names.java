package com.oracle.svm.hosted.sideeffects;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import com.oracle.graal.pointsto.export.PointsToExport;

import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * How the side-effect analysis names methods, fields and the places of nodes: as the export and
 * the tool name them, to look up what the tool says, and shorter, for the counts.
 */
final class Names {

    private Names() {
    }

    /**
     * Whether a method belongs to the program that {@code program} names, as
     * {@link PointsToExport#isProgramClass(String, String)} takes it.
     */
    static boolean inProgram(ResolvedJavaMethod method, String program) {
        return PointsToExport.isProgramClass(method.getDeclaringClass().toJavaName(true), program);
    }

    /**
     * A method as the export names it: LoadStoreElimination.length(LLoadStoreElimination$Link;)I.
     */
    static String exportName(ResolvedJavaMethod method) {
        return method.getDeclaringClass().toJavaName(true) + "." + method.getName() + method.getSignature().toMethodDescriptor();
    }

    /**
     * A method as the counts name it, for reading: LoadStoreElimination.length(Link).
     */
    static String readableName(ResolvedJavaMethod method) {
        String parameters = IntStream.range(0, method.getSignature().getParameterCount(false))
                        .mapToObj(i -> simpleName(method.getSignature().getParameterType(i, null).toJavaName(true)))
                        .collect(Collectors.joining(", "));
        return method.getDeclaringClass().toJavaName(false) + "." + method.getName() + "(" + parameters + ")";
    }

    /** A field as the export names it: Aliasing$Counter.value. */
    static String fieldName(ResolvedJavaField field) {
        return field.getDeclaringClass().toJavaName(true) + "." + field.getName();
    }

    /** A class's name without its package and the classes it is nested in. */
    static String simpleName(String name) {
        return name.substring(Math.max(name.lastIndexOf('.'), name.lastIndexOf('$')) + 1);
    }

    /**
     * A field as the reports name it: Aliasing$Counter.value is Counter.value.
     */
    static String shortField(String field) {
        int dot = field.lastIndexOf('.');
        return simpleName(field.substring(0, dot)) + field.substring(dot);
    }

    /**
     * The sites a node at {@code position} may be named by in the analysis's facts: its own, then
     * the same without each outermost caller in turn. A site names a node of the graph the facts
     * were taken from, innermost frame first (m:21 in c:4); inlining a copy of that graph into a
     * caller appends the caller's frame (m:21 in c:4 in h:7). A fact that holds in a graph holds
     * in every copy of it: an access's partition covers every context it is reached in.
     */
    static List<String> sitesOf(String position) {
        List<String> sites = new ArrayList<>();
        String site = position;
        while (true) {
            sites.add(site);
            int outermost = site.lastIndexOf(" in ");
            if (outermost < 0) {
                return sites;
            }
            site = site.substring(0, outermost);
        }
    }
}
