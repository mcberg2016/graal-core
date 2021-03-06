/*
 * Copyright (c) 2015, 2016, Oracle and/or its affiliates. All rights reserved.
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
package com.oracle.graal.compiler.test.tutorial;

import static com.oracle.graal.compiler.common.CompilationRequestIdentifier.asCompilationRequest;

import java.lang.reflect.Method;

import com.oracle.graal.api.test.Graal;
import com.oracle.graal.code.CompilationResult;
import com.oracle.graal.compiler.GraalCompiler;
import com.oracle.graal.compiler.common.CompilationIdentifier;
import com.oracle.graal.compiler.target.Backend;
import com.oracle.graal.debug.Debug;
import com.oracle.graal.debug.Debug.Scope;
import com.oracle.graal.debug.DebugDumpScope;
import com.oracle.graal.lir.asm.CompilationResultBuilderFactory;
import com.oracle.graal.lir.phases.LIRSuites;
import com.oracle.graal.nodes.StructuredGraph;
import com.oracle.graal.nodes.StructuredGraph.AllowAssumptions;
import com.oracle.graal.phases.OptimisticOptimizations;
import com.oracle.graal.phases.PhaseSuite;
import com.oracle.graal.phases.tiers.HighTierContext;
import com.oracle.graal.phases.tiers.Suites;
import com.oracle.graal.phases.util.Providers;
import com.oracle.graal.runtime.RuntimeProvider;

import jdk.vm.ci.code.CodeCacheProvider;
import jdk.vm.ci.code.InstalledCode;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ProfilingInfo;
import jdk.vm.ci.meta.ResolvedJavaMethod;

/**
 * Sample code that shows how to invoke Graal from an application.
 */
public class InvokeGraal {

    protected final Backend backend;
    protected final Providers providers;
    protected final MetaAccessProvider metaAccess;
    protected final CodeCacheProvider codeCache;

    public InvokeGraal() {
        /* Ask the hosting Java VM for the entry point object to the Graal API. */
        RuntimeProvider runtimeProvider = Graal.getRequiredCapability(RuntimeProvider.class);

        /*
         * The default backend (architecture, VM configuration) that the hosting VM is running on.
         */
        backend = runtimeProvider.getHostBackend();
        /* Access to all of the Graal API providers, as implemented by the hosting VM. */
        providers = backend.getProviders();
        /* Some frequently used providers and configuration objects. */
        metaAccess = providers.getMetaAccess();
        codeCache = providers.getCodeCache();
    }

    /**
     * The simplest way to compile a method, using the default behavior for everything.
     */
    @SuppressWarnings("try")
    protected InstalledCode compileAndInstallMethod(ResolvedJavaMethod method) {
        /* Create a unique compilation identifier, visible in IGV. */
        CompilationIdentifier compilationId = backend.getCompilationIdentifier(method);
        try (Scope s = Debug.scope("compileAndInstallMethod", new DebugDumpScope(String.valueOf(compilationId), true))) {

            /*
             * The graph that is compiled. We leave it empty (no nodes added yet). This means that
             * it will be filled according to the graphBuilderSuite defined below. We also specify
             * that we want the compilation to make optimistic assumptions about runtime state such
             * as the loaded class hierarchy.
             */
            StructuredGraph graph = new StructuredGraph(method, AllowAssumptions.YES, compilationId);

            /*
             * The phases used to build the graph. Usually this is just the GraphBuilderPhase. If
             * the graph already contains nodes, it is ignored.
             */
            PhaseSuite<HighTierContext> graphBuilderSuite = backend.getSuites().getDefaultGraphBuilderSuite();

            /*
             * The optimization phases that are applied to the graph. This is the main configuration
             * point for Graal. Add or remove phases to customize your compilation.
             */
            Suites suites = backend.getSuites().getDefaultSuites();

            /*
             * The low-level phases that are applied to the low-level representation.
             */
            LIRSuites lirSuites = backend.getSuites().getDefaultLIRSuites();

            /*
             * We want Graal to perform all speculative optimistic optimizations, using the
             * profiling information that comes with the method (collected by the interpreter) for
             * speculation.
             */
            OptimisticOptimizations optimisticOpts = OptimisticOptimizations.ALL;
            ProfilingInfo profilingInfo = graph.getProfilingInfo(method);

            /* The default class and configuration for compilation results. */
            CompilationResult compilationResult = new CompilationResult();
            CompilationResultBuilderFactory factory = CompilationResultBuilderFactory.Default;

            /* Invoke the whole Graal compilation pipeline. */
            GraalCompiler.compileGraph(graph, method, providers, backend, graphBuilderSuite, optimisticOpts, profilingInfo, suites, lirSuites, compilationResult, factory);

            /*
             * Install the compilation result into the VM, i.e., copy the byte[] array that contains
             * the machine code into an actual executable memory location.
             */
            return backend.addInstalledCode(method, asCompilationRequest(compilationId), compilationResult);
        } catch (Throwable ex) {
            throw Debug.handle(ex);
        }
    }

    /**
     * Look up a method using Java reflection and convert it to the Graal API method object.
     */
    protected ResolvedJavaMethod findMethod(Class<?> declaringClass, String name) {
        Method reflectionMethod = null;
        for (Method m : declaringClass.getDeclaredMethods()) {
            if (m.getName().equals(name)) {
                assert reflectionMethod == null : "More than one method with name " + name + " in class " + declaringClass.getName();
                reflectionMethod = m;
            }
        }
        assert reflectionMethod != null : "No method with name " + name + " in class " + declaringClass.getName();
        return metaAccess.lookupJavaMethod(reflectionMethod);
    }
}
