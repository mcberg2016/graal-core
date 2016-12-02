/*
 * Copyright (c) 2012, 2016, Oracle and/or its affiliates. All rights reserved.
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
package com.oracle.graal.loop.phases;

import com.oracle.graal.debug.Debug;
import com.oracle.graal.debug.DebugCounter;
import com.oracle.graal.loop.LoopEx;
import com.oracle.graal.loop.LoopPolicies;
import com.oracle.graal.loop.LoopsData;
import com.oracle.graal.nodes.StructuredGraph;
import com.oracle.graal.phases.common.CanonicalizerPhase;
import com.oracle.graal.phases.tiers.PhaseContext;

public class LoopInsertPrePostLoopsPhase extends LoopPhase<LoopPolicies> {

    private static final DebugCounter INSERT_PRE_POST_LOOPS = Debug.counter("InsertPrePostLoops");
    private final CanonicalizerPhase canonicalizer;

    public LoopInsertPrePostLoopsPhase(CanonicalizerPhase canonicalizer, LoopPolicies policies) {
        super(policies);
        this.canonicalizer = canonicalizer;
    }

    @Override
    protected void run(StructuredGraph graph, PhaseContext context) {
        if (graph.hasLoops()) {
            final LoopsData dataCounted = new LoopsData(graph);
            dataCounted.detectedCountedLoops();
            for (LoopEx loop : dataCounted.countedLoops()) {
                if (LoopTransformations.isQualifyingLoop(loop) == false) {
                    continue;
                }
                if (getPolicies().shouldEliminateRangeChecks(loop, context.getConstantReflection()) ||
                    getPolicies().shouldPartiallyUnroll(loop)) {
                    Debug.log("InsertPrePostLoops %s", loop);
                    LoopTransformations.insertPrePostLoops(loop, context, canonicalizer, graph);
                    INSERT_PRE_POST_LOOPS.increment();
                    Debug.dump(Debug.INFO_LOG_LEVEL, graph, "InsertPrePostLoops %s", loop);
                }
            }
            dataCounted.deleteUnusedNodes();
        }
        if (graph.hasLoops()) {
            // Really just for verification of the cfg
            final LoopsData dataCounted = new LoopsData(graph);
            dataCounted.detectedCountedLoops();
            dataCounted.deleteUnusedNodes();
            for (LoopEx loop : dataCounted.countedLoops()) {
                if (LoopTransformations.isQualifyingLoop(loop) == false) {
                    continue;
                }
            }
        }
    }

    @Override
    public boolean checkContract() {
        return false;
    }
}
