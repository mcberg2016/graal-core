/*
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved.
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
package com.oracle.graal.compiler.test;

import jdk.vm.ci.meta.JavaConstant;

import static com.oracle.graal.compiler.common.CompilationIdentifier.INVALID_COMPILATION_ID;

import org.junit.Assert;
import org.junit.Test;

import com.oracle.graal.nodes.ConstantNode;
import com.oracle.graal.nodes.ReturnNode;
import com.oracle.graal.nodes.StructuredGraph;
import com.oracle.graal.nodes.StructuredGraph.AllowAssumptions;
import com.oracle.graal.nodes.ValueNode;
import com.oracle.graal.nodes.calc.AddNode;
import com.oracle.graal.nodes.debug.OpaqueNode;
import com.oracle.graal.phases.common.CanonicalizerPhase;
import com.oracle.graal.phases.schedule.SchedulePhase;
import com.oracle.graal.phases.schedule.SchedulePhase.SchedulingStrategy;
import com.oracle.graal.phases.tiers.HighTierContext;

public class LongNodeChainTest extends GraalCompilerTest {

    public static final int N = 10000;

    private static final SchedulingStrategy[] Strategies = new SchedulingStrategy[]{SchedulingStrategy.EARLIEST};

    @Test
    public void testLongAddChain() {
        longAddChain(true);
        longAddChain(false);
    }

    private void longAddChain(boolean reverse) {
        HighTierContext context = getDefaultHighTierContext();
        StructuredGraph graph = new StructuredGraph(AllowAssumptions.NO, INVALID_COMPILATION_ID);
        ValueNode constant = graph.unique(ConstantNode.forPrimitive(JavaConstant.INT_1));
        ValueNode value = null;
        if (reverse) {
            // Make sure the constant's stamp is not used to infer the add node's stamp.
            OpaqueNode opaque = graph.unique(new OpaqueNode(constant));
            constant = opaque;
            AddNode addNode = graph.unique(new AddNode(constant, constant));
            value = addNode;
            for (int i = 1; i < N; ++i) {
                AddNode newAddNode = graph.addWithoutUnique(new AddNode(constant, constant));
                addNode.setY(newAddNode);
                addNode = newAddNode;
            }
            opaque.replaceAndDelete(opaque.getValue());
        } else {
            value = constant;
            for (int i = 0; i < N; ++i) {
                value = graph.unique(new AddNode(constant, value));
            }
        }
        ReturnNode returnNode = graph.add(new ReturnNode(value));
        graph.start().setNext(returnNode);

        for (SchedulingStrategy s : Strategies) {
            new SchedulePhase(s).apply(graph);
        }

        new CanonicalizerPhase().apply(graph, context);
        JavaConstant asConstant = (JavaConstant) returnNode.result().asConstant();
        Assert.assertEquals(N + 1, asConstant.asInt());
    }
}
