/*
 * Copyright (c) 2011, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
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
package com.oracle.graal.nodes;

import static com.oracle.graal.nodeinfo.NodeCycles.CYCLES_0;
import static com.oracle.graal.nodeinfo.NodeSize.SIZE_0;

import java.util.Arrays;
import java.util.Collections;

import com.oracle.graal.compiler.common.type.StampFactory;
import com.oracle.graal.graph.IterableNodeType;
import com.oracle.graal.graph.Node;
import com.oracle.graal.graph.NodeClass;
import com.oracle.graal.nodeinfo.NodeInfo;
import com.oracle.graal.nodes.spi.LIRLowerable;
import com.oracle.graal.nodes.spi.NodeLIRBuilderTool;

@NodeInfo(cycles = CYCLES_0, size = SIZE_0)
public abstract class AbstractEndNode extends FixedNode implements IterableNodeType, LIRLowerable {

    public static final NodeClass<AbstractEndNode> TYPE = NodeClass.create(AbstractEndNode.class);

    protected AbstractEndNode(NodeClass<? extends AbstractEndNode> c) {
        super(c, StampFactory.forVoid());
    }

    @Override
    public void generate(NodeLIRBuilderTool gen) {
        gen.visitEndNode(this);
    }

    public AbstractMergeNode merge() {
        return (AbstractMergeNode) usages().first();
    }

    @Override
    public boolean verify() {
        assertTrue(getUsageCount() <= 1, "at most one usage");
        return super.verify();
    }

    @Override
    public Iterable<? extends Node> cfgSuccessors() {
        AbstractMergeNode merge = merge();
        if (merge != null) {
            return Arrays.asList(merge);
        }
        return Collections.emptyList();
    }
}
