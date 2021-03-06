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
package com.oracle.graal.hotspot;

import static com.oracle.graal.hotspot.stubs.StubUtil.newDescriptor;

import java.util.EnumSet;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import com.oracle.graal.code.CompilationResult;
import com.oracle.graal.compiler.common.CompilationIdentifier;
import com.oracle.graal.compiler.common.cfg.AbstractBlockBase;
import com.oracle.graal.compiler.common.spi.ForeignCallDescriptor;
import com.oracle.graal.compiler.common.spi.ForeignCallLinkage;
import com.oracle.graal.compiler.target.Backend;
import com.oracle.graal.graph.Node.ConstantNodeParameter;
import com.oracle.graal.graph.Node.NodeIntrinsic;
import com.oracle.graal.hotspot.meta.HotSpotProviders;
import com.oracle.graal.hotspot.nodes.DeoptimizationFetchUnrollInfoCallNode;
import com.oracle.graal.hotspot.nodes.UncommonTrapCallNode;
import com.oracle.graal.hotspot.nodes.VMErrorNode;
import com.oracle.graal.hotspot.replacements.AESCryptSubstitutions;
import com.oracle.graal.hotspot.replacements.BigIntegerSubstitutions;
import com.oracle.graal.hotspot.replacements.CipherBlockChainingSubstitutions;
import com.oracle.graal.hotspot.replacements.SHA2Substitutions;
import com.oracle.graal.hotspot.replacements.SHA5Substitutions;
import com.oracle.graal.hotspot.replacements.SHASubstitutions;
import com.oracle.graal.hotspot.stubs.DeoptimizationStub;
import com.oracle.graal.hotspot.stubs.ExceptionHandlerStub;
import com.oracle.graal.hotspot.stubs.Stub;
import com.oracle.graal.hotspot.stubs.UnwindExceptionToCallerStub;
import com.oracle.graal.hotspot.word.KlassPointer;
import com.oracle.graal.lir.LIR;
import com.oracle.graal.lir.LIRFrameState;
import com.oracle.graal.lir.LIRInstruction;
import com.oracle.graal.lir.LIRInstruction.OperandFlag;
import com.oracle.graal.lir.LIRInstruction.OperandMode;
import com.oracle.graal.lir.StandardOp.LabelOp;
import com.oracle.graal.lir.StandardOp.SaveRegistersOp;
import com.oracle.graal.lir.ValueConsumer;
import com.oracle.graal.lir.asm.CompilationResultBuilder;
import com.oracle.graal.lir.framemap.FrameMap;
import com.oracle.graal.nodes.UnwindNode;
import com.oracle.graal.nodes.extended.ForeignCallNode;
import com.oracle.graal.options.Option;
import com.oracle.graal.options.OptionType;
import com.oracle.graal.options.OptionValue;
import com.oracle.graal.phases.tiers.SuitesProvider;
import com.oracle.graal.word.Pointer;
import com.oracle.graal.word.Word;

import jdk.vm.ci.code.CompilationRequest;
import jdk.vm.ci.code.CompiledCode;
import jdk.vm.ci.code.DebugInfo;
import jdk.vm.ci.code.Register;
import jdk.vm.ci.code.RegisterSaveLayout;
import jdk.vm.ci.code.StackSlot;
import jdk.vm.ci.code.ValueUtil;
import jdk.vm.ci.hotspot.HotSpotCompilationRequest;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntime;
import jdk.vm.ci.hotspot.HotSpotResolvedJavaMethod;
import jdk.vm.ci.meta.ResolvedJavaMethod;
import jdk.vm.ci.meta.Value;
import jdk.vm.ci.runtime.JVMCICompiler;

/**
 * HotSpot specific backend.
 */
public abstract class HotSpotBackend extends Backend implements FrameMap.ReferenceMapBuilderFactory {

    public static class Options {
        // @formatter:off
        @Option(help = "Use Graal stubs instead of HotSpot stubs where possible")
        public static final OptionValue<Boolean> PreferGraalStubs = new OptionValue<>(false);
        @Option(help = "Use Graal arithmetic stubs instead of HotSpot stubs where possible")
        public static final OptionValue<Boolean> GraalArithmeticStubs = new OptionValue<>(true);
        @Option(help = "Enables instruction profiling on assembler level. Valid values are a comma separated list of supported instructions." +
                        " Compare with subclasses of Assembler.InstructionCounter.", type = OptionType.Debug)
        public static final OptionValue<String> ASMInstructionProfiling = new OptionValue<>(null);
        // @formatter:on
    }

    /**
     * Descriptor for {@link ExceptionHandlerStub}. This stub is called by the
     * {@linkplain GraalHotSpotVMConfig#MARKID_EXCEPTION_HANDLER_ENTRY exception handler} in a
     * compiled method.
     */
    public static final ForeignCallDescriptor EXCEPTION_HANDLER = new ForeignCallDescriptor("exceptionHandler", void.class, Object.class, Word.class);

    /**
     * Descriptor for SharedRuntime::get_ic_miss_stub().
     */
    public static final ForeignCallDescriptor IC_MISS_HANDLER = new ForeignCallDescriptor("icMissHandler", void.class);

    /**
     * Descriptor for {@link UnwindExceptionToCallerStub}. This stub is called by code generated
     * from {@link UnwindNode}.
     */
    public static final ForeignCallDescriptor UNWIND_EXCEPTION_TO_CALLER = new ForeignCallDescriptor("unwindExceptionToCaller", void.class, Object.class, Word.class);

    /**
     * Descriptor for the arguments when unwinding to an exception handler in a caller.
     */
    public static final ForeignCallDescriptor EXCEPTION_HANDLER_IN_CALLER = new ForeignCallDescriptor("exceptionHandlerInCaller", void.class, Object.class, Word.class);

    private final HotSpotGraalRuntimeProvider runtime;

    /**
     * @see DeoptimizationFetchUnrollInfoCallNode
     */
    public static final ForeignCallDescriptor FETCH_UNROLL_INFO = new ForeignCallDescriptor("fetchUnrollInfo", Word.class, long.class, int.class);

    /**
     * @see DeoptimizationStub#unpackFrames(ForeignCallDescriptor, Word, int)
     */
    public static final ForeignCallDescriptor UNPACK_FRAMES = newDescriptor(DeoptimizationStub.class, "unpackFrames", int.class, Word.class, int.class);

    /**
     * @see AESCryptSubstitutions#encryptBlockStub(ForeignCallDescriptor, Word, Word, Pointer)
     */
    public static final ForeignCallDescriptor ENCRYPT_BLOCK = new ForeignCallDescriptor("encrypt_block", void.class, Word.class, Word.class, Pointer.class);

    /**
     * @see AESCryptSubstitutions#decryptBlockStub(ForeignCallDescriptor, Word, Word, Pointer)
     */
    public static final ForeignCallDescriptor DECRYPT_BLOCK = new ForeignCallDescriptor("decrypt_block", void.class, Word.class, Word.class, Pointer.class);

    /**
     * @see AESCryptSubstitutions#decryptBlockStub(ForeignCallDescriptor, Word, Word, Pointer)
     */
    public static final ForeignCallDescriptor DECRYPT_BLOCK_WITH_ORIGINAL_KEY = new ForeignCallDescriptor("decrypt_block_with_original_key", void.class, Word.class, Word.class, Pointer.class,
                    Pointer.class);

    /**
     * @see CipherBlockChainingSubstitutions#crypt
     */
    public static final ForeignCallDescriptor ENCRYPT = new ForeignCallDescriptor("encrypt", void.class, Word.class, Word.class, Pointer.class, Pointer.class, int.class);

    /**
     * @see CipherBlockChainingSubstitutions#crypt
     */
    public static final ForeignCallDescriptor DECRYPT = new ForeignCallDescriptor("decrypt", void.class, Word.class, Word.class, Pointer.class, Pointer.class, int.class);

    /**
     * @see CipherBlockChainingSubstitutions#crypt
     */
    public static final ForeignCallDescriptor DECRYPT_WITH_ORIGINAL_KEY = new ForeignCallDescriptor("decrypt_with_original_key", void.class, Word.class, Word.class, Pointer.class, Pointer.class,
                    int.class, Pointer.class);

    /**
     * @see BigIntegerSubstitutions#multiplyToLen
     */
    public static final ForeignCallDescriptor MULTIPLY_TO_LEN = new ForeignCallDescriptor("multiplyToLen", void.class, Word.class, int.class, Word.class, int.class, Word.class, int.class);

    public static void multiplyToLenStub(Word xAddr, int xlen, Word yAddr, int ylen, Word zAddr, int zLen) {
        multiplyToLenStub(HotSpotBackend.MULTIPLY_TO_LEN, xAddr, xlen, yAddr, ylen, zAddr, zLen);
    }

    @NodeIntrinsic(ForeignCallNode.class)
    private static native void multiplyToLenStub(@ConstantNodeParameter ForeignCallDescriptor descriptor, Word xIn, int xLen, Word yIn, int yLen, Word zIn, int zLen);

    /**
     * @see BigIntegerSubstitutions#mulAdd
     */
    public static final ForeignCallDescriptor MUL_ADD = new ForeignCallDescriptor("mulAdd", int.class, Word.class, Word.class, int.class, int.class, int.class);

    public static int mulAddStub(Word inAddr, Word outAddr, int newOffset, int len, int k) {
        return mulAddStub(HotSpotBackend.MUL_ADD, inAddr, outAddr, newOffset, len, k);
    }

    @NodeIntrinsic(ForeignCallNode.class)
    private static native int mulAddStub(@ConstantNodeParameter ForeignCallDescriptor descriptor, Word inAddr, Word outAddr, int newOffset, int len, int k);

    /**
     * @see BigIntegerSubstitutions#implMontgomeryMultiply
     */
    public static final ForeignCallDescriptor MONTGOMERY_MULTIPLY = new ForeignCallDescriptor("implMontgomeryMultiply", void.class, Word.class, Word.class, Word.class, int.class, long.class,
                    Word.class);

    public static void implMontgomeryMultiply(Word aAddr, Word bAddr, Word nAddr, int len, long inv, Word productAddr) {
        implMontgomeryMultiply(HotSpotBackend.MONTGOMERY_MULTIPLY, aAddr, bAddr, nAddr, len, inv, productAddr);
    }

    @NodeIntrinsic(ForeignCallNode.class)
    private static native void implMontgomeryMultiply(@ConstantNodeParameter ForeignCallDescriptor descriptor, Word aAddr, Word bAddr, Word nAddr, int len, long inv, Word productAddr);

    /**
     * @see BigIntegerSubstitutions#implMontgomerySquare
     */
    public static final ForeignCallDescriptor MONTGOMERY_SQUARE = new ForeignCallDescriptor("implMontgomerySquare", void.class, Word.class, Word.class, int.class, long.class, Word.class);

    public static void implMontgomerySquare(Word aAddr, Word nAddr, int len, long inv, Word productAddr) {
        implMontgomerySquare(HotSpotBackend.MONTGOMERY_SQUARE, aAddr, nAddr, len, inv, productAddr);
    }

    @NodeIntrinsic(ForeignCallNode.class)
    private static native void implMontgomerySquare(@ConstantNodeParameter ForeignCallDescriptor descriptor, Word aAddr, Word nAddr, int len, long inv, Word productAddr);

    /**
     * @see BigIntegerSubstitutions#implSquareToLen
     */
    public static final ForeignCallDescriptor SQUARE_TO_LEN = new ForeignCallDescriptor("implSquareToLen", void.class, Word.class, int.class, Word.class, int.class);

    public static void implSquareToLen(Word xAddr, int len, Word zAddr, int zLen) {
        implSquareToLen(SQUARE_TO_LEN, xAddr, len, zAddr, zLen);
    }

    @NodeIntrinsic(ForeignCallNode.class)
    private static native void implSquareToLen(@ConstantNodeParameter ForeignCallDescriptor descriptor, Word xAddr, int len, Word zAddr, int zLen);

    /**
     * @see SHASubstitutions#implCompress0
     */
    public static final ForeignCallDescriptor SHA_IMPL_COMPRESS = new ForeignCallDescriptor("shaImplCompress", void.class, Word.class, Object.class);

    public static void shaImplCompressStub(Word bufAddr, Object state) {
        shaImplCompressStub(HotSpotBackend.SHA_IMPL_COMPRESS, bufAddr, state);
    }

    @NodeIntrinsic(ForeignCallNode.class)
    private static native void shaImplCompressStub(@ConstantNodeParameter ForeignCallDescriptor descriptor, Word bufAddr, Object state);

    /**
     * @see SHA2Substitutions#implCompress0
     */
    public static final ForeignCallDescriptor SHA2_IMPL_COMPRESS = new ForeignCallDescriptor("sha2ImplCompress", void.class, Word.class, Object.class);

    public static void sha2ImplCompressStub(Word bufAddr, Object state) {
        sha2ImplCompressStub(HotSpotBackend.SHA2_IMPL_COMPRESS, bufAddr, state);
    }

    @NodeIntrinsic(ForeignCallNode.class)
    private static native void sha2ImplCompressStub(@ConstantNodeParameter ForeignCallDescriptor descriptor, Word bufAddr, Object state);

    /**
     * @see SHA5Substitutions#implCompress0
     */
    public static final ForeignCallDescriptor SHA5_IMPL_COMPRESS = new ForeignCallDescriptor("sha5ImplCompress", void.class, Word.class, Object.class);

    public static void sha5ImplCompressStub(Word bufAddr, Object state) {
        sha5ImplCompressStub(HotSpotBackend.SHA5_IMPL_COMPRESS, bufAddr, state);
    }

    @NodeIntrinsic(ForeignCallNode.class)
    private static native void sha5ImplCompressStub(@ConstantNodeParameter ForeignCallDescriptor descriptor, Word bufAddr, Object state);

    /**
     * @see VMErrorNode
     */
    public static final ForeignCallDescriptor VM_ERROR = new ForeignCallDescriptor("vm_error", void.class, Object.class, Object.class, long.class);

    /**
     * New multi array stub call.
     */
    public static final ForeignCallDescriptor NEW_MULTI_ARRAY = new ForeignCallDescriptor("new_multi_array", Object.class, KlassPointer.class, int.class, Word.class);

    /**
     * New array stub.
     */
    public static final ForeignCallDescriptor NEW_ARRAY = new ForeignCallDescriptor("new_array", Object.class, KlassPointer.class, int.class, boolean.class);

    /**
     * New instance stub.
     */
    public static final ForeignCallDescriptor NEW_INSTANCE = new ForeignCallDescriptor("new_instance", Object.class, KlassPointer.class);

    /**
     * @see UncommonTrapCallNode
     */
    public static final ForeignCallDescriptor UNCOMMON_TRAP = new ForeignCallDescriptor("uncommonTrap", Word.class, Word.class, int.class, int.class);

    public HotSpotBackend(HotSpotGraalRuntimeProvider runtime, HotSpotProviders providers) {
        super(providers);
        this.runtime = runtime;
    }

    public HotSpotGraalRuntimeProvider getRuntime() {
        return runtime;
    }

    /**
     * Performs any remaining initialization that was deferred until the {@linkplain #getRuntime()
     * runtime} object was initialized and this backend was registered with it.
     *
     * @param jvmciRuntime
     */
    public void completeInitialization(HotSpotJVMCIRuntime jvmciRuntime) {
    }

    /**
     * Finds all the registers that are defined by some given LIR.
     *
     * @param lir the LIR to examine
     * @return the registers that are defined by or used as temps for any instruction in {@code lir}
     */
    protected final Set<Register> gatherDestroyedCallerRegisters(LIR lir) {
        final Set<Register> destroyedRegisters = new HashSet<>();
        ValueConsumer defConsumer = new ValueConsumer() {

            @Override
            public void visitValue(Value value, OperandMode mode, EnumSet<OperandFlag> flags) {
                if (ValueUtil.isRegister(value)) {
                    final Register reg = ValueUtil.asRegister(value);
                    destroyedRegisters.add(reg);
                }
            }
        };
        for (AbstractBlockBase<?> block : lir.codeEmittingOrder()) {
            if (block == null) {
                continue;
            }
            for (LIRInstruction op : lir.getLIRforBlock(block)) {
                if (op instanceof LabelOp) {
                    // Don't consider this as a definition
                } else {
                    op.visitEachTemp(defConsumer);
                    op.visitEachOutput(defConsumer);
                }
            }
        }
        return translateToCallerRegisters(destroyedRegisters);
    }

    /**
     * Updates a given stub with respect to the registers it destroys.
     * <p>
     * Any entry in {@code calleeSaveInfo} that {@linkplain SaveRegistersOp#supportsRemove()
     * supports} pruning will have {@code destroyedRegisters}
     * {@linkplain SaveRegistersOp#remove(Set) removed} as these registers are declared as
     * temporaries in the stub's {@linkplain ForeignCallLinkage linkage} (and thus will be saved by
     * the stub's caller).
     *
     * @param stub the stub to update
     * @param destroyedRegisters the registers destroyed by the stub
     * @param calleeSaveInfo a map from debug infos to the operations that provide their
     *            {@linkplain RegisterSaveLayout callee-save information}
     * @param frameMap used to {@linkplain FrameMap#offsetForStackSlot(StackSlot) convert} a virtual
     *            slot to a frame slot index
     */
    protected void updateStub(Stub stub, Set<Register> destroyedRegisters, Map<LIRFrameState, SaveRegistersOp> calleeSaveInfo, FrameMap frameMap) {
        stub.initDestroyedCallerRegisters(destroyedRegisters);

        for (Map.Entry<LIRFrameState, SaveRegistersOp> e : calleeSaveInfo.entrySet()) {
            SaveRegistersOp save = e.getValue();
            if (save.supportsRemove()) {
                save.remove(destroyedRegisters);
            }
            DebugInfo info = e.getKey() == null ? null : e.getKey().debugInfo();
            if (info != null) {
                info.setCalleeSaveInfo(save.getMap(frameMap));
            }
        }
    }

    @Override
    public HotSpotProviders getProviders() {
        return (HotSpotProviders) super.getProviders();
    }

    @Override
    public SuitesProvider getSuites() {
        return getProviders().getSuites();
    }

    protected void profileInstructions(LIR lir, CompilationResultBuilder crb) {
        if (HotSpotBackend.Options.ASMInstructionProfiling.getValue() != null) {
            HotSpotInstructionProfiling.countInstructions(lir, crb.asm);
        }
    }

    @Override
    public CompiledCode createCompiledCode(ResolvedJavaMethod method, CompilationRequest compilationRequest, CompilationResult compResult) {
        HotSpotCompilationRequest compRequest = compilationRequest instanceof HotSpotCompilationRequest ? (HotSpotCompilationRequest) compilationRequest : null;
        return HotSpotCompiledCodeBuilder.createCompiledCode(method, compRequest, compResult);
    }

    @Override
    public CompilationIdentifier getCompilationIdentifier(ResolvedJavaMethod resolvedJavaMethod) {
        if (resolvedJavaMethod instanceof HotSpotResolvedJavaMethod) {
            HotSpotCompilationRequest request = new HotSpotCompilationRequest((HotSpotResolvedJavaMethod) resolvedJavaMethod, JVMCICompiler.INVOCATION_ENTRY_BCI, 0L);
            return new HotSpotCompilationIdentifier(request);
        }
        return super.getCompilationIdentifier(resolvedJavaMethod);
    }
}
