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
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import com.oracle.graal.pointsto.export.PointsToExport;

import jdk.vm.ci.meta.ResolvedJavaField;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Names for methods, fields and node positions: the export's names, to look things up in the
 * tool's output, and shorter names for the counts.
 */
final class Names {

    private Names() {
    }

    /** Whether a method is part of the program, as {@link PointsToExport#isProgramClass(String, String)} decides. */
    static boolean inProgram(ResolvedJavaMethod method, String program) {
        return PointsToExport.isProgramClass(method.getDeclaringClass().toJavaName(true), program);
    }

    /**
     * A method's name in the export, e.g. {@code LoadStoreElimination.length(LLoadStoreElimination$Link;)I}.
     * Lambda classes are named by content, not by the address this build gave them.
     */
    static String exportName(ResolvedJavaMethod method) {
        return PointsToExport.methodKey(method);
    }

    /** A method's short name in the counts, e.g. {@code LoadStoreElimination.length(Link)}. */
    static String readableName(ResolvedJavaMethod method) {
        String parameters = IntStream.range(0, method.getSignature().getParameterCount(false))
                        .mapToObj(i -> simpleName(method.getSignature().getParameterType(i, null).toJavaName(true)))
                        .collect(Collectors.joining(", "));
        return method.getDeclaringClass().toJavaName(false) + "." + method.getName() + "(" + parameters + ")";
    }

    /** A field's name in the export, e.g. {@code Aliasing$Counter.value}; lambda classes by content. */
    static String fieldName(ResolvedJavaField field) {
        return PointsToExport.fieldName(field);
    }

    /** A class name without its package and enclosing classes. */
    static String simpleName(String name) {
        return name.substring(Math.max(name.lastIndexOf('.'), name.lastIndexOf('$')) + 1);
    }

    /** A field's short name in reports: {@code Aliasing$Counter.value} becomes {@code Counter.value}. */
    static String shortField(String field) {
        int dot = field.lastIndexOf('.');
        return simpleName(field.substring(0, dot)) + field.substring(dot);
    }

    /**
     * The positions under which facts about a node at {@code position} may be recorded: the full
     * position, then the same with the outermost caller removed, one at a time. A position lists
     * frames innermost first ({@code m:21 in c:4}); inlining that graph into a caller appends the
     * caller's frame ({@code m:21 in c:4 in h:7}). A fact about a graph holds in every copy of it, so
     * a shorter match is still valid.
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
