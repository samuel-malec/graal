/*
 * Copyright (c) 2016, 2018, Oracle and/or its affiliates. All rights reserved.
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
package jdk.graal.compiler.nodes;

import java.util.Objects;

import org.graalvm.word.LocationIdentity;

import jdk.vm.ci.meta.JavaKind.FormatWithToString;
import jdk.vm.ci.meta.ResolvedJavaField;

public class FieldLocationIdentity extends LocationIdentity implements FormatWithToString {

    private final ResolvedJavaField inner;
    private final boolean immutable;
    /** Which part of the field this is, null for all of it: see {@link #getPartition()}. */
    private final Object partition;

    public FieldLocationIdentity(ResolvedJavaField inner) {
        this(inner, false);
    }

    public FieldLocationIdentity(ResolvedJavaField inner, boolean immutable) {
        this(inner, immutable, null);
    }

    public FieldLocationIdentity(ResolvedJavaField inner, boolean immutable, Object partition) {
        this.inner = inner;
        this.immutable = immutable;
        this.partition = partition;
    }

    /**
     * The partition of the objects that have the field this location stands for, or null for all
     * of them. A points-to analysis can split a field's objects into partitions that no access
     * spans; locations of different partitions are then different memory. Since locations only
     * overlap when they are equal, a graph must give every access to a field a partition, or
     * none.
     */
    public Object getPartition() {
        return partition;
    }

    @Override
    public boolean isImmutable() {
        return immutable;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj instanceof FieldLocationIdentity) {
            FieldLocationIdentity fieldLocationIdentity = (FieldLocationIdentity) obj;
            return inner.equals(fieldLocationIdentity.inner) && immutable == fieldLocationIdentity.immutable && Objects.equals(partition, fieldLocationIdentity.partition);
        }
        return false;
    }

    public ResolvedJavaField getField() {
        return inner;
    }

    @Override
    public int hashCode() {
        return partition == null ? Objects.hash(inner, immutable) : Objects.hash(inner, immutable, partition);
    }

    @Override
    public String toString() {
        return inner.format("%H.%n") + (partition != null ? "@" + partition : "") + (isImmutable() ? ":immutable" : "");
    }
}
