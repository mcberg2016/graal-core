/*
 * Copyright (c) 2012, 2012, Oracle and/or its affiliates. All rights reserved.
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

import static com.oracle.graal.compiler.common.GraalOptions.MaximumDesiredSize;
import static jdk.vm.ci.meta.DeoptimizationReason.BoundsCheckException;
import static jdk.vm.ci.meta.DeoptimizationReason.NullCheckException;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import com.oracle.graal.graph.Graph.Mark;
import com.oracle.graal.compiler.common.cfg.Loop;
import com.oracle.graal.compiler.common.type.IntegerStamp;
import com.oracle.graal.compiler.common.type.Stamp;
import com.oracle.graal.compiler.common.type.StampFactory;
import com.oracle.graal.debug.Debug;
import com.oracle.graal.graph.Node;
import com.oracle.graal.graph.Position;
import com.oracle.graal.loop.BasicInductionVariable;
import com.oracle.graal.loop.CountedLoopInfo;
import com.oracle.graal.loop.InductionVariable;
import com.oracle.graal.loop.LoopEx;
import com.oracle.graal.loop.LoopFragmentWhole;
import com.oracle.graal.loop.InductionVariable.Direction;
import static com.oracle.graal.loop.MathUtil.add;
import static com.oracle.graal.loop.MathUtil.sub;
import com.oracle.graal.nodeinfo.InputType;
import com.oracle.graal.nodes.AbstractBeginNode;
import com.oracle.graal.nodes.AbstractEndNode;
import com.oracle.graal.nodes.AbstractMergeNode;
import com.oracle.graal.nodes.BeginNode;
import com.oracle.graal.nodes.BinaryOpLogicNode;
import com.oracle.graal.nodes.ConstantNode;
import com.oracle.graal.nodes.ControlSplitNode;
import com.oracle.graal.nodes.DeoptimizeNode;
import com.oracle.graal.nodes.EndNode;
import com.oracle.graal.nodes.FixedNode;
import com.oracle.graal.nodes.FixedWithNextNode;
import com.oracle.graal.nodes.GuardNode;
import com.oracle.graal.nodes.IfNode;
import com.oracle.graal.nodes.LogicNode;
import com.oracle.graal.nodes.LoopBeginNode;
import com.oracle.graal.nodes.LoopExitNode;
import com.oracle.graal.nodes.MergeNode;
import com.oracle.graal.nodes.NamedLocationIdentity;
import com.oracle.graal.nodes.PhiNode;
import com.oracle.graal.nodes.PiNode;
import com.oracle.graal.nodes.StructuredGraph;
import com.oracle.graal.nodes.ValueNode;
import com.oracle.graal.nodes.ValuePhiNode;
import com.oracle.graal.nodes.calc.AddNode;
import com.oracle.graal.nodes.calc.BinaryArithmeticNode;
import com.oracle.graal.nodes.calc.CompareNode;
import com.oracle.graal.nodes.calc.IntegerBelowNode;
import com.oracle.graal.nodes.calc.IntegerEqualsNode;
import com.oracle.graal.nodes.calc.IntegerLessThanNode;
import com.oracle.graal.nodes.calc.SignExtendNode;
import com.oracle.graal.nodes.calc.SubNode;
import com.oracle.graal.nodes.calc.ZeroExtendNode;
import com.oracle.graal.nodes.cfg.Block;
import com.oracle.graal.nodes.extended.GuardingNode;
import com.oracle.graal.nodes.extended.SwitchNode;
import com.oracle.graal.nodes.memory.ReadNode;
import com.oracle.graal.nodes.memory.WriteNode;
import com.oracle.graal.nodes.memory.HeapAccess.BarrierType;
import com.oracle.graal.nodes.memory.address.AddressNode;
import com.oracle.graal.nodes.memory.address.OffsetAddressNode;
import com.oracle.graal.phases.common.CanonicalizerPhase;
import com.oracle.graal.phases.tiers.PhaseContext;

import jdk.vm.ci.code.BailoutException;
import jdk.vm.ci.meta.JavaKind;

public abstract class LoopTransformations {

    private LoopTransformations() {
        // does not need to be instantiated
    }

    public static void peel(LoopEx loop) {
        loop.inside().duplicate().insertBefore(loop);
        loop.loopBegin().setLoopFrequency(Math.max(0.0, loop.loopBegin().loopFrequency() - 1));
    }

    public static void fullUnroll(LoopEx loop, PhaseContext context, CanonicalizerPhase canonicalizer) {
        // assert loop.isCounted(); //TODO (gd) strengthen : counted with known trip count
        LoopBeginNode loopBegin = loop.loopBegin();
        StructuredGraph graph = loopBegin.graph();
        int initialNodeCount = graph.getNodeCount();
        while (!loopBegin.isDeleted()) {
            Mark mark = graph.getMark();
            peel(loop);
            canonicalizer.applyIncremental(graph, context, mark);
            loop.invalidateFragments();
            if (graph.getNodeCount() > initialNodeCount + MaximumDesiredSize.getValue() * 2) {
                throw new BailoutException("FullUnroll : Graph seems to grow out of proportion");
            }
        }
    }

    public static void unswitch(LoopEx loop, List<ControlSplitNode> controlSplitNodeSet) {
        ControlSplitNode firstNode = controlSplitNodeSet.iterator().next();
        LoopFragmentWhole originalLoop = loop.whole();
        StructuredGraph graph = firstNode.graph();

        loop.loopBegin().incrementUnswitches();

        // create new control split out of loop
        ControlSplitNode newControlSplit = (ControlSplitNode) firstNode.copyWithInputs();
        originalLoop.entryPoint().replaceAtPredecessor(newControlSplit);

        /*
         * The code below assumes that all of the control split nodes have the same successor
         * structure, which should have been enforced by findUnswitchable.
         */
        Iterator<Position> successors = firstNode.successorPositions().iterator();
        assert successors.hasNext();
        // original loop is used as first successor
        Position firstPosition = successors.next();
        AbstractBeginNode originalLoopBegin = BeginNode.begin(originalLoop.entryPoint());
        firstPosition.set(newControlSplit, originalLoopBegin);

        while (successors.hasNext()) {
            Position position = successors.next();
            // create a new loop duplicate and connect it.
            LoopFragmentWhole duplicateLoop = originalLoop.duplicate();
            AbstractBeginNode newBegin = BeginNode.begin(duplicateLoop.entryPoint());
            position.set(newControlSplit, newBegin);

            // For each cloned ControlSplitNode, simplify the proper path
            for (ControlSplitNode controlSplitNode : controlSplitNodeSet) {
                ControlSplitNode duplicatedControlSplit = duplicateLoop.getDuplicatedNode(controlSplitNode);
                if (duplicatedControlSplit.isAlive()) {
                    AbstractBeginNode survivingSuccessor = (AbstractBeginNode) position.get(duplicatedControlSplit);
                    survivingSuccessor.replaceAtUsages(InputType.Guard, newBegin);
                    graph.removeSplitPropagate(duplicatedControlSplit, survivingSuccessor);
                }
            }
        }
        // original loop is simplified last to avoid deleting controlSplitNode too early
        for (ControlSplitNode controlSplitNode : controlSplitNodeSet) {
            if (controlSplitNode.isAlive()) {
                AbstractBeginNode survivingSuccessor = (AbstractBeginNode) firstPosition.get(controlSplitNode);
                survivingSuccessor.replaceAtUsages(InputType.Guard, originalLoopBegin);
                graph.removeSplitPropagate(controlSplitNode, survivingSuccessor);
            }
        }

        // TODO (gd) probabilities need some amount of fixup.. (probably also in other transforms)
    }

    public static void insertPrePostLoops(LoopEx loop, PhaseContext context, CanonicalizerPhase canonicalizer, StructuredGraph graph) {
        LoopFragmentWhole preLoop = loop.whole();
        LoopBeginNode preLoopBegin = loop.loopBegin();
        EndNode preEndNode = null;
        LoopExitNode preLoopExit = null;
        for (LoopExitNode curLoopExit : preLoopBegin.loopExits()) {
            preEndNode = (EndNode) curLoopExit.next();
            preLoopExit = curLoopExit;
            break;
        }
        CountedLoopInfo preCounted = preLoop.loop().counted();
        IfNode preLimit = preCounted.getLimitTest();
        ValueNode preInit = preCounted.getStart();
        int phiIndex = -1;

        // TODO: Check for compound limit cases, the addition of value tests to guard main
        // may introduce too much code.

        loop.loopBegin().incrementSplits();

        // Each duplication is inserted after the original, so we need to make the post loop first
        // then the main
        LoopFragmentWhole postLoop = preLoop.duplicate();
        LoopFragmentWhole mainLoop = preLoop.duplicate();

        // Now process the main loop
        LoopBeginNode mainLoopBegin = mainLoop.getDuplicatedNode(loop.loopBegin());
        EndNode mainEndNode = null;
        for (LoopExitNode mainLoopExit : mainLoopBegin.loopExits()) {
            mainEndNode = (EndNode) mainLoopExit.next();
            break;
        }
        AbstractBeginNode mainBeginNode = BeginNode.begin(mainLoop.entryPoint());
        BasicInductionVariable preIv = (BasicInductionVariable) preCounted.getCounter();

        EndNode postLandingEnd = graph.add(new EndNode());
        AbstractBeginNode postLandingNode = graph.add(new BeginNode());
        postLandingNode.setNext(postLandingEnd);

        if (preLimit != null) {
            List<Node> workList = new ArrayList<>();
            // update main loops array access nodes without guards
            for (Node preNode : preLoop.loop().inside().nodes()) {
                Node node = mainLoop.getDuplicatedNode(preNode);
                if (node instanceof ReadNode) {
                    ReadNode readNode = (ReadNode) node;
                    GuardNode guard = (GuardNode) readNode.getGuard();
                    if (guard == null) {
                        continue;
                    }
                    if ((guard.getReason() == BoundsCheckException) || (guard.getReason() == NullCheckException)) {
                        AddressNode address = readNode.getAddress();
                        ReadNode memoryRead = graph.add(new ReadNode(address, readNode.getLocationIdentity(), readNode.stamp(), BarrierType.NONE));
                        graph.replaceFixed(readNode, memoryRead);
                        workList.add(guard);
                    }
                } else if (node instanceof WriteNode) {
                    WriteNode writeNode = (WriteNode) node;
                    GuardNode guard = (GuardNode) writeNode.getGuard();
                    if (guard == null) {
                        continue;
                    }
                    if ((guard.getReason() == BoundsCheckException) || (guard.getReason() == NullCheckException)) {
                        AddressNode address = writeNode.getAddress();
                        ValueNode value = writeNode.value();
                        WriteNode memoryWrite = graph.add(new WriteNode(address, writeNode.getLocationIdentity(), value, writeNode.getBarrierType()));
                        graph.replaceFixed(writeNode, memoryWrite);
                        workList.add(guard);
                    }
                } else if (node instanceof PiNode) {
                    PiNode piNode = (PiNode) node;
                    GuardNode guard = (GuardNode) piNode.getGuard();
                    if (guard == null) {
                        continue;
                    }
                    if (guard.getReason() == BoundsCheckException) {
                        PiNode replacement = graph.addWithoutUnique(new PiNode(piNode.getOriginalNode(), piNode.stamp()));
                        piNode.replaceAtUsages(replacement);
                        piNode.safeDelete();
                    }
                }
            }

            for (Node node : workList) {
                GuardNode guard = (GuardNode) node;
                LogicNode condition = guard.getCondition();
                if (guard.hasNoUsages()) {
                    guard.safeDelete();
                }
                if (condition.hasNoUsages()) {
                    condition.safeDelete();
                }
            }

            // update mains iv initialization so that the pre loops iv reaches mains init
            PhiNode prePhiNode = (PhiNode) preIv.valueNode();
            PhiNode mainPhiNode = mainLoop.getDuplicatedNode(prePhiNode);
            AbstractEndNode forwardEnd = preLoopBegin.forwardEnd();
            ValueNode phiInit = prePhiNode.valueAt(forwardEnd);
            int numInputs = prePhiNode.valueCount();
            for (int i = 0; i < numInputs; i++) {
                ValueNode curValue = prePhiNode.valueAt(i);
                if (curValue == preInit) {
                    mainPhiNode.initializeValueAt(i, prePhiNode);
                    phiIndex = i;
                    break;
                }
            }
        }

        // Now process the post loop
        LoopBeginNode postLoopBegin = postLoop.getDuplicatedNode(loop.loopBegin());
        AbstractBeginNode postBeginNode = BeginNode.begin(postLoop.entryPoint());
        EndNode postEndNode = null;
        for (LoopExitNode postLoopExit : postLoopBegin.loopExits()) {
            postEndNode = (EndNode) postLoopExit.next();
            break;
        }

        if (preLimit != null) {
            // update post loops array access nodes without null checks
            for (Node preNode : preLoop.loop().inside().nodes()) {
                Node node = postLoop.getDuplicatedNode(preNode);
                if (node instanceof ReadNode) {
                    ReadNode readNode = (ReadNode) node;
                    GuardNode guard = (GuardNode) readNode.getGuard();
                    if (guard == null) {
                        continue;
                    }
                    if (guard.getReason() == NullCheckException) {
                        AddressNode address = readNode.getAddress();
                        ReadNode memoryRead = graph.add(new ReadNode(address, readNode.getLocationIdentity(), readNode.stamp(), BarrierType.NONE));
                        graph.replaceFixed(readNode, memoryRead);
                    }
                } else if (node instanceof WriteNode) {
                    WriteNode writeNode = (WriteNode) node;
                    GuardNode guard = (GuardNode) writeNode.getGuard();
                    if (guard == null) {
                        continue;
                    }
                    if (guard.getReason() == NullCheckException) {
                        AddressNode address = writeNode.getAddress();
                        ValueNode value = writeNode.value();
                        WriteNode memoryWrite = graph.add(new WriteNode(address, writeNode.getLocationIdentity(), value, writeNode.getBarrierType()));
                        graph.replaceFixed(writeNode, memoryWrite);
                    }
                }
            }
        }

        PhiNode postPhiNode = postLoop.getDuplicatedNode(preIv.valueNode());
        ValueNode origLimit = preIv.exitValueNode();

        // Add limit based range checks to guard main loop entry
        if (origLimit != null) {
            List<Node> boundsExpressions = findBoundsExpressions(preLoop.loop());
            AbstractBeginNode mainBypassChecks;
            IfNode ifNode = null;
            IfNode firstIf = null;
            IfNode lastIf = null;
            GuardNode lastGuard = null;

            // Now manually lower the bounds expressions to IfNodes so that the branch side
            // is connected to the post loop and the fall side to either the
            // next bounds check or to the main loop.
            for (Node node : boundsExpressions) {
                LogicNode condition = null;
                GuardNode guard = null;
                if (node instanceof ReadNode) {
                    ReadNode readNode = (ReadNode) node;
                    guard = (GuardNode) readNode.getGuard();
                    condition = guard.getCondition();
                } else if (node instanceof WriteNode) {
                    WriteNode writeNode = (WriteNode) node;
                    guard = (GuardNode) writeNode.getGuard();
                    condition = guard.getCondition();
                }

                // Now if we found a valid condition we use it to construct our flow
                if (condition != null) {
                    // We are going to replace the iv check with the limit from the post loop
                    // as we will never be changing it.
                    if (condition instanceof BinaryOpLogicNode) {
                        BinaryOpLogicNode logicNode = (BinaryOpLogicNode) condition;
                        ValueNode arrayLength = logicNode.getY();
                        // The x argument of the binary logic node initially contained the current
                        // index, we will replace it with the post loop limit.
                        IntegerBelowNode ifTest = new IntegerBelowNode(origLimit, arrayLength);
                        AbstractBeginNode trueSuccessor;
                        AbstractBeginNode falseSuccessor;
                        if (guard.isNegated()) {
                            trueSuccessor = postLandingNode;
                            falseSuccessor = mainBeginNode;
                        } else {
                            trueSuccessor = mainBeginNode;
                            falseSuccessor = postLandingNode;
                        }
                        ifNode = graph.add(new IfNode(ifTest, trueSuccessor, falseSuccessor, trueSuccessor == mainBeginNode ? 1 : 0));
                        if (lastIf != null) {
                            mainBypassChecks = BeginNode.begin(ifNode);
                            if (lastGuard.isNegated()) {
                                lastIf.setFalseSuccessor(mainBypassChecks);
                            } else {
                                lastIf.setTrueSuccessor(mainBypassChecks);
                            }
                        } else {
                            firstIf = ifNode;
                        }
                        lastGuard = guard;
                        lastIf = ifNode;
                    }
                }
            }

            // Now create a place for the zero trip guard to go to if we are 
            // out of iterations after main.
            EndNode finalLandingEnd = graph.add(new EndNode());
            AbstractBeginNode finalLandingNode = graph.add(new BeginNode());
            finalLandingNode.setNext(finalLandingEnd);

            // Fix up uses for merge nodes so that each loop has flow destination
            // We do this because the duplication code was written for flow joins and not
            // sequential loops.
            AbstractMergeNode mainMergeNode = mainEndNode.merge();
            if (firstIf != null) {
                AbstractMergeNode preMergeNode = preEndNode.merge();
                FixedNode oldMergeNext = preMergeNode.next();
                preMergeNode.setNext(firstIf);

                EndNode oldMainBypassEnd = mainMergeNode.forwardEndAt(0);
                oldMainBypassEnd.safeDelete();
                mainMergeNode.clearEnds();
                mainMergeNode.addForwardEnd(mainEndNode);
                mainMergeNode.addForwardEnd(postLandingEnd);
                mainMergeNode.next().safeDelete();

                AbstractMergeNode postMergeNode = postEndNode.merge();
                postMergeNode.clearEnds();
                postMergeNode.addForwardEnd(postEndNode);
                postMergeNode.addForwardEnd(finalLandingEnd);
                postMergeNode.setNext(oldMergeNext);
                preLoopExit.setNext(preEndNode);
            }

            // Add a phi that carries the final value of the iv of both main and pre
            // to update post loops iv initialization.
            JavaKind elementKind = postPhiNode.getStackKind();
            Stamp postInitValueStamp = StampFactory.forKind(elementKind);
            ValuePhiNode mergeIvValues = graph.addWithoutUnique(new ValuePhiNode(postInitValueStamp, mainEndNode.merge()));
            ValueNode preTripValue = (ValueNode) preIv.getOp();
            ValueNode mainTripValue = (ValueNode) mainLoop.getDuplicatedNode(preIv.getOp());
            mergeIvValues.addInput(preTripValue);
            mergeIvValues.addInput(mainTripValue);
            postPhiNode.initializeValueAt(phiIndex, mergeIvValues);

            // now add a zero trip guard over the post loop
            if (origLimit != null) {
                IntegerEqualsNode ifTest = new IntegerEqualsNode(origLimit, mergeIvValues);
                ifNode = graph.add(new IfNode(ifTest, finalLandingNode, postBeginNode, 0));
                mainMergeNode.setNext(ifNode);
            }

            // Update the pre loops limit test
            if (preLimit != null) {
                LogicNode ifTest = preLimit.condition();
                CompareNode lessThan = (CompareNode) ifTest;
                ValueNode varX = null;
                ValueNode varY = null;
                ValueNode prePhi = (ValueNode) preIv.valueNode();

                // Fetch the variable we are not replacing and configure the one we are
                if (lessThan.getX() == prePhi) {
                    varX = prePhi;
                } else if (lessThan.getY() == prePhi) {
                    varY = prePhi;
                }

                // Check direction and make new limit one iteration
                ValueNode initIv = preCounted.getStart();
                ValueNode newLimit = null;
                if (preIv.direction() == Direction.Up) {
                    newLimit = add(graph, initIv, preIv.strideNode());
                } else {
                    newLimit = sub(graph, initIv, preIv.strideNode());
                }

                // Now replace the old limit
                if (varX == null) {
                    varX = newLimit;
                } else {
                    varY = newLimit;
                }

                // Re-wire the new condition into preLimit
                if (ifTest instanceof IntegerLessThanNode) {
                    LogicNode newIfTest = graph.addWithoutUnique(new IntegerLessThanNode(varX, varY));
                    ifTest.replaceAtUsages(newIfTest);
                    ifTest.safeDelete();
                } else if (ifTest instanceof IntegerEqualsNode) {
                    LogicNode newIfTest = graph.addWithoutUnique(new IntegerEqualsNode(varX, varY));
                    ifTest.replaceAtUsages(newIfTest);
                    ifTest.safeDelete();
                }
            }
        }
    }

    public static List<Node> findBoundsExpressions(LoopEx loop) {
        List<Node> boundsExpressions = null;
        for (Node node : loop.inside().nodes()) {
            boolean foundCandidate = false;
            if (node instanceof ReadNode) {
                ReadNode readNode = (ReadNode) node;
                if (readNode.getGuard() != null) {
                    GuardingNode guarding = readNode.getGuard();
                    if (guarding instanceof GuardNode) {
                        GuardNode guard = (GuardNode) guarding;
                        if (guard.getReason() == BoundsCheckException) {
                            foundCandidate = true;
                        }
                    }
                }
            } else if (node instanceof WriteNode) {
                WriteNode writeNode = (WriteNode) node;
                if (writeNode.getGuard() != null) {
                    GuardingNode guarding = writeNode.getGuard();
                    if (guarding instanceof GuardNode) {
                        GuardNode guard = (GuardNode) guarding;
                        if (guard.getReason() == BoundsCheckException) {
                            foundCandidate = true;
                        }
                    }
                }
            }
            if (foundCandidate) {
                if (boundsExpressions == null) {
                    boundsExpressions = new ArrayList<>();
                    boundsExpressions.add(node);
                } else if (isUniqueAddress(node, boundsExpressions) == true) {
                    boundsExpressions.add(node);
                }
            }
        }
        return boundsExpressions;
    }

    public static boolean isUniqueAddress(Node inNode, List<Node> boundsExpressions) {
        boolean isUniqueAddress = true;
        boolean checkRead = true;
        OffsetAddressNode offsetAddress = null;
        if (inNode instanceof ReadNode) {
            ReadNode readNode = (ReadNode) inNode;
            offsetAddress = (OffsetAddressNode) readNode.getAddress();
        } else if (inNode instanceof WriteNode) {
            WriteNode writeNode = (WriteNode) inNode;
            offsetAddress = (OffsetAddressNode) writeNode.getAddress();
            checkRead = false;
        }
        if (offsetAddress != null) {
            for (Node node : boundsExpressions) {
                if (node instanceof ReadNode) {
                    // always compare same type
                    if (checkRead == false) {
                        continue;
                    }
                    ReadNode validNode = (ReadNode) node;
                    OffsetAddressNode validOffsetAddress = (OffsetAddressNode) validNode.getAddress();
                    // If two reads have the same base address, and we already know they are
                    // guarded, that is sufficient since we know the guards are bounds checks.
                    if (validOffsetAddress.getBase() == offsetAddress.getBase()) {
                        isUniqueAddress = false;
                        break;
                    }
                } else if (node instanceof WriteNode) {
                    // always compare same type
                    if (checkRead) {
                        continue;
                    }
                    WriteNode validNode = (WriteNode) node;
                    OffsetAddressNode validOffsetAddress = (OffsetAddressNode) validNode.getAddress();
                    // If two writes have the same base address, and we already know they are
                    // guarded, that is sufficient since we know the guards are bounds checks.
                    if (validOffsetAddress.getBase() == offsetAddress.getBase()) {
                        isUniqueAddress = false;
                        break;
                    }
                }
            }
        }
        return isUniqueAddress;
    }

    public static List<ControlSplitNode> findUnswitchable(LoopEx loop) {
        List<ControlSplitNode> controls = null;
        ValueNode invariantValue = null;
        for (IfNode ifNode : loop.whole().nodes().filter(IfNode.class)) {
            if (loop.isOutsideLoop(ifNode.condition())) {
                if (controls == null) {
                    invariantValue = ifNode.condition();
                    controls = new ArrayList<>();
                    controls.add(ifNode);
                } else if (ifNode.condition() == invariantValue) {
                    controls.add(ifNode);
                }
            }
        }
        if (controls == null) {
            SwitchNode firstSwitch = null;
            for (SwitchNode switchNode : loop.whole().nodes().filter(SwitchNode.class)) {
                if (switchNode.successors().count() > 1 && loop.isOutsideLoop(switchNode.value())) {
                    if (controls == null) {
                        firstSwitch = switchNode;
                        invariantValue = switchNode.value();
                        controls = new ArrayList<>();
                        controls.add(switchNode);
                    } else if (switchNode.value() == invariantValue && firstSwitch.structureEquals(switchNode)) {
                        // Only collect switches which test the same values in the same order
                        controls.add(switchNode);
                    }
                }
            }
        }
        return controls;
    }

    public static boolean isQualifyingLoop(LoopEx loop) {
        boolean isInnerLoop = true;
        Loop<Block> curLoop = loop.loop();
        for (Loop<Block> child : curLoop.getChildren()) {
            isInnerLoop = false;
            break;
        }
        if (isInnerLoop) {
            CountedLoopInfo counted = loop.counted();
            InductionVariable iv = counted.getCounter();
            // Does this loop have unit stride?
            if (iv.isConstantStride() && Math.abs(iv.constantStride()) == 1) {
                AbstractBeginNode curBeginNode = (AbstractBeginNode) loop.loopBegin();
                LoopBeginNode curLoopBegin = (LoopBeginNode) curBeginNode;
                int exitCount = 0;
                for (LoopExitNode exit : curLoopBegin.loopExits()) {
                    exitCount++;
                }
                // Does this loop have a single exit?
                if (exitCount == 1) {
                    boolean isCanonical = true;
                    // One last check, see if there are other kinds of excepting guards that we
                    // cannot eliminate
                    for (Node node : loop.inside().nodes()) {
                        if (node instanceof GuardNode) {
                            GuardNode guard = (GuardNode) node;
                            if ((guard.getReason() != BoundsCheckException) && (guard.getReason() != NullCheckException)) {
                                isCanonical = false;
                                break;
                            }
                        }
                    }
                    return isCanonical;
                } else {
                    return false;
                }
            }
        }
        return false;
    }
}
