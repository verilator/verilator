// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: main()
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#define VL_MT_CONTROL_CODE_UNIT 1

#include "V3Active.h"
#include "V3ActiveTop.h"
#include "V3Assert.h"
#include "V3AssertPre.h"
#include "V3Ast.h"
#include "V3Begin.h"
#include "V3Branch.h"
#include "V3Broken.h"
#include "V3CCtors.h"
#include "V3CUse.h"
#include "V3Case.h"
#include "V3Cast.h"
#include "V3Class.h"
#include "V3Clean.h"
#include "V3Clock.h"
#include "V3Combine.h"
#include "V3Common.h"
#include "V3Const.h"
#include "V3Coverage.h"
#include "V3CoverageJoin.h"
#include "V3Dead.h"
#include "V3Delayed.h"
#include "V3Depth.h"
#include "V3DepthBlock.h"
#include "V3Descope.h"
#include "V3DfgOptimizer.h"
#include "V3EmitC.h"
#include "V3EmitCMain.h"
#include "V3EmitCMake.h"
#include "V3EmitMk.h"
#include "V3EmitV.h"
#include "V3EmitXml.h"
#include "V3Expand.h"
#include "V3File.h"
#include "V3Force.h"
#include "V3Fork.h"
#include "V3Gate.h"
#include "V3Global.h"
#include "V3Graph.h"
#include "V3HierBlock.h"
#include "V3Inline.h"
#include "V3Inst.h"
#include "V3Interface.h"
#include "V3Life.h"
#include "V3LifePost.h"
#include "V3LinkDot.h"
#include "V3LinkInc.h"
#include "V3LinkJump.h"
#include "V3LinkLValue.h"
#include "V3LinkLevel.h"
#include "V3LinkParse.h"
#include "V3LinkResolve.h"
#include "V3Localize.h"
#include "V3MergeCond.h"
#include "V3Name.h"
#include "V3Os.h"
#include "V3Param.h"
#include "V3ParseSym.h"
#include "V3Partition.h"
#include "V3PreShell.h"
#include "V3Premit.h"
#include "V3ProtectLib.h"
#include "V3Randomize.h"
#include "V3Reloop.h"
#include "V3Sched.h"
#include "V3Scope.h"
#include "V3Scoreboard.h"
#include "V3Slice.h"
#include "V3Split.h"
#include "V3SplitAs.h"
#include "V3SplitVar.h"
#include "V3Stats.h"
#include "V3String.h"
#include "V3Subst.h"
#include "V3TSP.h"
#include "V3Table.h"
#include "V3Task.h"
#include "V3ThreadPool.h"
#include "V3Timing.h"
#include "V3Trace.h"
#include "V3TraceDecl.h"
#include "V3Tristate.h"
#include "V3Undriven.h"
#include "V3Unknown.h"
#include "V3Unroll.h"
#include "V3VariableOrder.h"
#include "V3Waiver.h"
#include "V3Width.h"
#include "V3WidthCommit.h"

#include <ctime>

VL_DEFINE_DEBUG_FUNCTIONS;

V3Global v3Global;

static void reportStatsIfEnabled() {
    if (v3Global.opt.stats()) {
        V3Stats::statsFinalAll(v3Global.rootp());
        V3Stats::statsReport();
    }
}

static void emitJson() VL_MT_DISABLED {
    const string filename
        = (v3Global.opt.jsonOnlyOutput().empty()
               ? v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + ".tree.json"
               : v3Global.opt.jsonOnlyOutput());
    v3Global.rootp()->dumpTreeJsonFile(filename);
}

static void emitXmlOrJson() VL_MT_DISABLED {
    if (v3Global.opt.xmlOnly()) V3EmitXml::emitxml();
    if (v3Global.opt.jsonOnly()) emitJson();
}

static void process() {
    {
        const V3MtDisabledLockGuard mtDisabler{v3MtDisabledLock()};
        // Sort modules by level so later algorithms don't need to care
        V3LinkLevel::modSortByLevel();
        V3Error::abortIfErrors();
        if (v3Global.opt.debugExitParse()) {
            cout << "--debug-exit-parse: Exiting after parse\n";
            std::exit(0);
        }

        // Convert parseref's to varrefs, and other directly post parsing fixups
        V3LinkParse::linkParse(v3Global.rootp());
        // Cross-link signal names
        // Cross-link dotted hierarchical references
        V3LinkDot::linkDotPrimary(v3Global.rootp());
        v3Global.checkTree();  // Force a check, as link is most likely place for problems
        // Check if all parameters have been found
        v3Global.opt.checkParameters();
        // Correct state we couldn't know at parse time, repair SEL's
        V3LinkResolve::linkResolve(v3Global.rootp());
        // Set Lvalue's in variable refs
        V3LinkLValue::linkLValue(v3Global.rootp());
        // Convert return/continue/disable to jumps
        V3LinkJump::linkJump(v3Global.rootp());
        // Convert --/++ to normal operations. Must be after LinkJump.
        V3LinkInc::linkIncrements(v3Global.rootp());
        V3Error::abortIfErrors();

        if (v3Global.opt.stats()) V3Stats::statsStageAll(v3Global.rootp(), "Link");
        if (v3Global.opt.debugExitUvm23()) {
            V3Error::abortIfErrors();
            if (v3Global.opt.serializeOnly()) emitXmlOrJson();
            cout << "--debug-exit-uvm23: Exiting after UVM-supported pass\n";
            std::exit(0);
        }

        // Remove parameters by cloning modules to de-parameterized versions
        //   This requires some width calculations and constant propagation
        V3Param::param(v3Global.rootp());
        V3LinkDot::linkDotParamed(v3Global.rootp());  // Cleanup as made new modules
        V3LinkLValue::linkLValue(v3Global.rootp());  // Resolve new VarRefs
        V3Error::abortIfErrors();

        // Remove any modules that were parameterized and are no longer referenced.
        V3Dead::deadifyModules(v3Global.rootp());
        v3Global.checkTree();

        // Create a hierarchical Verilation plan
        if (!v3Global.opt.lintOnly() && !v3Global.opt.serializeOnly()
            && v3Global.opt.hierarchical()) {
            V3HierBlockPlan::createPlan(v3Global.rootp());
            // If a plan is created, further analysis is not necessary.
            // The actual Verilation will be done based on this plan.
            if (v3Global.hierPlanp()) {
                reportStatsIfEnabled();
                return;
            }
        }
        if (v3Global.opt.debugExitUvm()) {
            V3Error::abortIfErrors();
            if (v3Global.opt.serializeOnly()) emitXmlOrJson();
            cout << "--debug-exit-uvm: Exiting after UVM-supported pass\n";
            std::exit(0);
        }

        // Calculate and check widths, edit tree to TRUNC/EXTRACT any width mismatches
        V3Width::width(v3Global.rootp());

        V3Error::abortIfErrors();

        // Commit to the widths we've chosen; Make widthMin==width
        V3WidthCommit::widthCommit(v3Global.rootp());
        v3Global.assertDTypesResolved(true);
        v3Global.widthMinUsage(VWidthMinUsage::MATCHES_WIDTH);

        // Coverage insertion
        //    Before we do dead code elimination and inlining, or we'll lose it.
        if (v3Global.opt.coverage()) V3Coverage::coverage(v3Global.rootp());

        // Add randomize() class methods if they are used by the design
        if (v3Global.useRandomizeMethods()) V3Randomize::randomizeNetlist(v3Global.rootp());

        // Push constants, but only true constants preserving liveness
        // so V3Undriven sees variables to be eliminated, ie "if (0 && foo) ..."
        if (v3Global.opt.fConstBeforeDfg()) V3Const::constifyAllLive(v3Global.rootp());

        // Signal based lint checks, no change to structures
        // Must be before first constification pass drops dead code
        V3Undriven::undrivenAll(v3Global.rootp());

        // Assertion insertion
        //    After we've added block coverage, but before other nasty transforms
        V3AssertPre::assertPreAll(v3Global.rootp());
        //
        V3Assert::assertAll(v3Global.rootp());

        if (!(v3Global.opt.serializeOnly() && !v3Global.opt.flatten())) {
            // Add top level wrapper with instance pointing to old top
            // Move packages to under new top
            // Must do this after we know parameters and dtypes (as don't clone dtype decls)
            V3LinkLevel::wrapTop(v3Global.rootp());
        }

        // Propagate constants into expressions
        if (v3Global.opt.fConstBeforeDfg()) V3Const::constifyAllLint(v3Global.rootp());

        if (!(v3Global.opt.serializeOnly() && !v3Global.opt.flatten())) {
            // Split packed variables into multiple pieces to resolve UNOPTFLAT.
            // should be after constifyAllLint() which flattens to 1D bit vector
            V3SplitVar::splitVariable(v3Global.rootp());

            // Remove cell arrays (must be between V3Width and scoping)
            V3Inst::dearrayAll(v3Global.rootp());
            V3LinkDot::linkDotArrayed(v3Global.rootp());

            if (v3Global.opt.timing().isSetTrue()) {
                // Generate classes and tasks required to maintain proper lifetimes for references
                // in forks
                V3Fork::makeDynamicScopes(v3Global.rootp());
                V3Fork::makeTasks(v3Global.rootp());
            }

            // Task inlining & pushing BEGINs names to variables/cells
            // Begin processing must be after Param, before module inlining
            V3Begin::debeginAll(v3Global.rootp());  // Flatten cell names, before inliner

            // Expand inouts, stage 2
            // Also simplify pin connections to always be AssignWs in prep for V3Unknown
            V3Tristate::tristateAll(v3Global.rootp());
        }

        if (!v3Global.opt.serializeOnly()) {
            // Move assignments from X into MODULE temps.
            // (Before flattening, so each new X variable is shared between all scopes of that
            // module.)
            V3Unknown::unknownAll(v3Global.rootp());
            v3Global.constRemoveXs(true);
        }

        if (v3Global.opt.fDfgPreInline() || v3Global.opt.fDfgPostInline()) {
            // If doing DFG optimization, extract some additional candidates
            V3DfgOptimizer::extract(v3Global.rootp());
        }

        if (v3Global.opt.fDfgPreInline()) {
            // Pre inline DFG optimization
            V3DfgOptimizer::optimize(v3Global.rootp(), "pre inline");
        }

        if (!(v3Global.opt.serializeOnly() && !v3Global.opt.flatten())) {
            // Module inlining
            // Cannot remove dead variables after this, as alias information for final
            // V3Scope's V3LinkDot is in the AstVar.
            if (v3Global.opt.fInline()) {
                V3Inline::inlineAll(v3Global.rootp());
                V3LinkDot::linkDotArrayed(v3Global.rootp());  // Cleanup as made new modules
            }
        }

        if (v3Global.opt.trace()) V3Interface::interfaceAll(v3Global.rootp());

        if (v3Global.opt.fDfgPostInline()) {
            // Post inline DFG optimization
            V3DfgOptimizer::optimize(v3Global.rootp(), "post inline");
        }

        // --PRE-FLAT OPTIMIZATIONS------------------

        // Initial const/dead to reduce work for ordering code
        V3Const::constifyAll(v3Global.rootp());
        v3Global.checkTree();

        V3Dead::deadifyDTypes(v3Global.rootp());
        v3Global.checkTree();

        V3Error::abortIfErrors();

        // --FLATTENING---------------

        if (!(v3Global.opt.serializeOnly() && !v3Global.opt.flatten())) {
            // We're going to flatten the hierarchy, so as many optimizations that
            // can be done as possible should be before this....

            // Convert instantiations to wassigns and always blocks
            V3Inst::instAll(v3Global.rootp());

            // Inst may have made lots of concats; fix them
            V3Const::constifyAll(v3Global.rootp());

            // Flatten hierarchy, creating a SCOPE for each module's usage as a cell
            V3Scope::scopeAll(v3Global.rootp());
            V3LinkDot::linkDotScope(v3Global.rootp());

            // Relocate classes (after linkDot)
            V3Class::classAll(v3Global.rootp());
        }

        // --SCOPE BASED OPTIMIZATIONS--------------

        if (!(v3Global.opt.serializeOnly() && !v3Global.opt.flatten())) {
            // Cleanup
            V3Const::constifyAll(v3Global.rootp());
            V3Dead::deadifyDTypesScoped(v3Global.rootp());
            v3Global.checkTree();
        }

        if (!v3Global.opt.serializeOnly()) {
            // Convert case statements to if() blocks.  Must be after V3Unknown
            // Must be before V3Task so don't need to deal with task in case value compares
            V3Case::caseAll(v3Global.rootp());
        }

        if (!(v3Global.opt.serializeOnly() && !v3Global.opt.flatten())) {
            // Inline all tasks
            V3Task::taskAll(v3Global.rootp());
        }

        if (!v3Global.opt.serializeOnly()) {
            // Add __PVT's
            // After V3Task so task internal variables will get renamed
            V3Name::nameAll(v3Global.rootp());

            // Loop unrolling & convert FORs to WHILEs
            V3Unroll::unrollAll(v3Global.rootp());

            // Expand slices of arrays
            V3Slice::sliceAll(v3Global.rootp());

            // Push constants across variables and remove redundant assignments
            V3Const::constifyAll(v3Global.rootp());

            if (v3Global.opt.fLife()) V3Life::lifeAll(v3Global.rootp());

            // Make large low-fanin logic blocks into lookup tables
            // This should probably be done much later, once we have common logic elimination.
            if (!v3Global.opt.lintOnly() && v3Global.opt.fTable()) {
                V3Table::tableAll(v3Global.rootp());
            }

            // Cleanup
            V3Const::constifyAll(v3Global.rootp());
            V3Dead::deadifyDTypesScoped(v3Global.rootp());
            v3Global.checkTree();

            // Move assignments/sensitives into a SBLOCK for each unique sensitivity list
            // (May convert some ALWAYS to combo blocks, so should be before V3Gate step.)
            V3Active::activeAll(v3Global.rootp());

            // Split single ALWAYS blocks into multiple blocks for better ordering chances
            if (v3Global.opt.fSplit()) V3Split::splitAlwaysAll(v3Global.rootp());
            V3SplitAs::splitAsAll(v3Global.rootp());

            // Create tracing sample points, before we start eliminating signals
            if (v3Global.opt.trace()) V3TraceDecl::traceDeclAll(v3Global.rootp());

            // Convert forceable signals, process force/release statements.
            // After V3TraceDecl so we don't trace additional signals inserted to implement
            // forcing.
            V3Force::forceAll(v3Global.rootp());

            // Gate-based logic elimination; eliminate signals and push constant across cell
            // boundaries Instant propagation makes lots-o-constant reduction possibilities.
            if (v3Global.opt.fGate()) {
                V3Gate::gateAll(v3Global.rootp());
                // V3Gate calls constant propagation itself.
            } else {
                v3info("Command Line disabled gate optimization with -fno-gate.  "
                       "This may cause ordering problems.");
            }

            // Combine COVERINCs with duplicate terms
            if (v3Global.opt.coverage()) V3CoverageJoin::coverageJoin(v3Global.rootp());

            // Remove unused vars
            V3Const::constifyAll(v3Global.rootp());
            V3Dead::deadifyAllScoped(v3Global.rootp());

            // Reorder assignments in pipelined blocks
            if (v3Global.opt.fReorder()) V3Split::splitReorderAll(v3Global.rootp());

            if (v3Global.opt.timing().isSetTrue()) {
                // Convert AST for timing if requested
                // Needs to be after V3Gate, as that step modifies sentrees
                // Needs to be before V3Delayed, as delayed assignments are handled differently in
                // suspendable processes
                V3Timing::timingAll(v3Global.rootp());
            }

            // Create delayed assignments
            // This creates lots of duplicate ACTIVES so ActiveTop needs to be after this step
            V3Delayed::delayedAll(v3Global.rootp());

            // Make Active's on the top level.
            // Differs from V3Active, because identical clocks may be pushed
            // down to a module and now be identical
            V3ActiveTop::activeTopAll(v3Global.rootp());

            if (v3Global.opt.stats()) V3Stats::statsStageAll(v3Global.rootp(), "PreOrder");

            // Schedule the logic
            V3Sched::schedule(v3Global.rootp());

            // Convert sense lists into IF statements.
            V3Clock::clockAll(v3Global.rootp());

            // Cleanup any dly vars or other temps that are simple assignments
            // Life must be done before Subst, as it assumes each CFunc under
            // _eval is called only once.
            if (v3Global.opt.fLife()) {
                V3Const::constifyAll(v3Global.rootp());
                V3Life::lifeAll(v3Global.rootp());
            }

            if (v3Global.opt.fLifePost()) V3LifePost::lifepostAll(v3Global.rootp());

            // Remove unused vars
            V3Const::constifyAll(v3Global.rootp());
            V3Dead::deadifyAllScoped(v3Global.rootp());

            // Create tracing logic, since we ripped out some signals the user might want to trace
            // Note past this point, we presume traced variables won't move between CFuncs
            // (It's OK if untraced temporaries move around, or vars
            // "effectively" activate the same way.)
            if (v3Global.opt.trace()) V3Trace::traceAll(v3Global.rootp());

            if (v3Global.opt.stats()) V3Stats::statsStageAll(v3Global.rootp(), "Scoped");
        }

        // --MODULE OPTIMIZATIONS--------------

        if (!v3Global.opt.serializeOnly()) {
            // Split deep blocks to appease MSVC++.  Must be before Localize.
            if (!v3Global.opt.lintOnly() && v3Global.opt.compLimitBlocks()) {
                V3DepthBlock::depthBlockAll(v3Global.rootp());
            }

            // Up until this point, all references must be scoped
            v3Global.assertScoped(false);

            // Move variables from modules to function local variables where possible
            if (v3Global.opt.fLocalize()) V3Localize::localizeAll(v3Global.rootp());

            // Remove remaining scopes; make varrefs/funccalls relative to current module
            V3Descope::descopeAll(v3Global.rootp());

            // Icache packing; combine common code in each module's functions into subroutines
            if (v3Global.opt.fCombine()) V3Combine::combineAll(v3Global.rootp());
        }

        V3Error::abortIfErrors();

        // --GENERATION------------------

        if (!v3Global.opt.serializeOnly()) {
            // Remove unused vars
            V3Const::constifyAll(v3Global.rootp());
            V3Dead::deadifyAll(v3Global.rootp());

            // Here down, widthMin() is the Verilog width, and width() is the C++ width
            // Bits between widthMin() and width() are irrelevant, but may be non zero.
            v3Global.widthMinUsage(VWidthMinUsage::VERILOG_WIDTH);

            // Make all expressions either 8, 16, 32 or 64 bits
            V3Clean::cleanAll(v3Global.rootp());

            // Move wide constants to BLOCK temps / ConstPool.
            V3Premit::premitAll(v3Global.rootp());
        }

        // Expand macros and wide operators into C++ primitives
        if (!v3Global.opt.lintOnly() && !v3Global.opt.serializeOnly() && v3Global.opt.fExpand()) {
            V3Expand::expandAll(v3Global.rootp());
        }

        // Propagate constants across WORDSEL arrayed temporaries
        if (!v3Global.opt.serializeOnly() && v3Global.opt.fSubst()) {
            // Constant folding of expanded stuff
            V3Const::constifyCpp(v3Global.rootp());
            V3Subst::substituteAll(v3Global.rootp());
        }

        if (!v3Global.opt.serializeOnly() && v3Global.opt.fSubstConst()) {
            // Constant folding of substitutions
            V3Const::constifyCpp(v3Global.rootp());
            V3Dead::deadifyAll(v3Global.rootp());
        }

        if (!v3Global.opt.lintOnly() && !v3Global.opt.serializeOnly()) {
            if (v3Global.opt.fMergeCond()) {
                // Merge conditionals
                V3MergeCond::mergeAll(v3Global.rootp());
            }

            if (v3Global.opt.fReloop()) {
                // Reform loops to reduce code size
                // Must be after all Sel/array index based optimizations
                V3Reloop::reloopAll(v3Global.rootp());
            }

            // Fix very deep expressions
            // Mark evaluation functions as member functions, if needed.
            V3Depth::depthAll(v3Global.rootp());

            // Branch prediction
            V3Branch::branchAll(v3Global.rootp());

            // Add C casts when longs need to become long-long and vice-versa
            // Note depth may insert something needing a cast, so this must be last.
            V3Cast::castAll(v3Global.rootp());
        }

        V3Error::abortIfErrors();
        if (!v3Global.opt.lintOnly() && !v3Global.opt.serializeOnly()) {  //
            V3CCtors::cctorsAll();
        }

        if (!v3Global.opt.serializeOnly() && v3Global.opt.mtasks()) {
            // Finalize our MTask cost estimates and pack the mtasks into
            // threads. Must happen pre-EmitC which relies on the packing
            // order. Must happen post-V3LifePost which changes the relative
            // costs of mtasks.
            V3Partition::finalize(v3Global.rootp());
        }

        if (!v3Global.opt.lintOnly() && !v3Global.opt.serializeOnly()
            && !v3Global.opt.dpiHdrOnly()) {
            // Add common methods/etc to modules
            V3Common::commonAll();

            // Order variables
            V3VariableOrder::orderAll();

            // Create AstCUse to determine what class forward declarations/#includes needed in C
            V3CUse::cUseAll();
        }

        // Output the text
        if (!v3Global.opt.lintOnly() && !v3Global.opt.serializeOnly()
            && !v3Global.opt.dpiHdrOnly()) {
            // emitcInlines is first, as it may set needHInlines which other emitters read
            V3EmitC::emitcInlines();
            V3EmitC::emitcSyms();
            V3EmitC::emitcConstPool();
            V3EmitC::emitcModel();
            V3EmitC::emitcPch();
            V3EmitC::emitcHeaders();
        } else if (v3Global.opt.dpiHdrOnly()) {
            V3EmitC::emitcSyms(true);
        }
    }
    if (!v3Global.opt.serializeOnly()
        && !v3Global.opt.dpiHdrOnly()) {  // Unfortunately we have some lint checks in emitcImp.
        V3EmitC::emitcImp();
    }
    {
        const V3MtDisabledLockGuard mtDisabler{v3MtDisabledLock()};
        if (v3Global.opt.serializeOnly()) {
            emitXmlOrJson();
        } else if (v3Global.opt.debugCheck() && !v3Global.opt.lintOnly()
                   && !v3Global.opt.dpiHdrOnly()) {
            // Check XML/JSON when debugging to make sure no missing node types
            V3EmitXml::emitxml();
            emitJson();
        }

        // Output DPI protected library files
        if (!v3Global.opt.libCreate().empty()) {
            if (v3Global.rootp()->delaySchedulerp()) {
                v3warn(E_UNSUPPORTED, "Unsupported: --lib-create with --timing and delays");
            }
            V3ProtectLib::protect();
            V3EmitV::emitvFiles();
            V3EmitC::emitcFiles();
        }

        if (!v3Global.opt.lintOnly() && !v3Global.opt.serializeOnly()
            && !v3Global.opt.dpiHdrOnly()) {
            if (v3Global.opt.main()) V3EmitCMain::emit();

            // V3EmitMk/V3EmitCMake must be after all other emitters,
            // as they and below code visits AstCFiles added earlier
            size_t src_f_cnt = 0;
            for (AstNode* nodep = v3Global.rootp()->filesp(); nodep; nodep = nodep->nextp()) {
                if (const AstCFile* cfilep = VN_CAST(nodep, CFile))
                    src_f_cnt += cfilep->source() ? 1 : 0;
            }
            if (src_f_cnt >= V3EmitMk::PARALLEL_FILE_CNT_THRESHOLD)
                v3Global.useParallelBuild(true);
            if (v3Global.opt.cmake()) V3EmitCMake::emit();
            if (v3Global.opt.gmake()) V3EmitMk::emitmk();
        }

        // Final statistics
        if (v3Global.opt.stats()) V3Stats::statsStage("emit");
        reportStatsIfEnabled();
    }
}

static void verilate(const string& argString) {
    UINFO(1, "Option --verilate: Start Verilation\n");

    // Can we skip doing everything if times are ok?
    V3File::addSrcDepend(v3Global.opt.buildDepBin());
    if (v3Global.opt.skipIdentical().isTrue()
        && V3File::checkTimes(v3Global.opt.hierTopDataDir() + "/" + v3Global.opt.prefix()
                                  + "__verFiles.dat",
                              argString)) {
        UINFO(1, "--skip-identical: No change to any source files, exiting\n");
        return;
    }
    // Undocumented debugging - cannot be a switch as then command line
    // would mismatch forcing non-identicalness when we set it
    if (!V3Os::getenvStr("VERILATOR_DEBUG_SKIP_IDENTICAL", "").empty()) {  // LCOV_EXCL_START
        v3fatalSrc("VERILATOR_DEBUG_SKIP_IDENTICAL w/ --skip-identical: Changes found\n");
    }  // LCOV_EXCL_STOP

    // Disable mutexes in single-thread verilation
    V3MutexConfig::s().configure(v3Global.opt.verilateJobs() > 1 /*enable*/);
    // Adjust thread pool size
    V3ThreadPool::s().resize(v3Global.opt.verilateJobs());

    // --FRONTEND------------------

    // Cleanup
    // Ideally we'd do prefix + "_*.*", and prefix + ".*", but this seems
    // potentially disruptive to old behavior, and --skip-identical
    V3Os::unlinkRegexp(v3Global.opt.hierTopDataDir(), v3Global.opt.prefix() + "_*.dot");
    V3Os::unlinkRegexp(v3Global.opt.hierTopDataDir(), v3Global.opt.prefix() + "_*.tree");
    V3Os::unlinkRegexp(v3Global.opt.hierTopDataDir(), v3Global.opt.prefix() + "_*.txt");

    // Internal tests (after option parsing as need debug() setting,
    // and after removing files as may make debug output)
    VBasicDTypeKwd::selfTest();
    if (v3Global.opt.debugSelfTest()) {
        {
            const V3MtDisabledLockGuard mtDisabler{v3MtDisabledLock()};

            V3Os::selfTest();
            VHashSha256::selfTest();
            VSpellCheck::selfTest();
            V3Graph::selfTest();
            V3TSP::selfTest();
            V3ScoreboardBase::selfTest();
            V3Partition::selfTest();
            V3Partition::selfTestNormalizeCosts();
            V3PreShell::selfTest();
            V3Broken::selfTest();
        }
        V3ThreadPool::selfTest();
        UINFO(2, "selfTest done\n");
    }

    {
        const V3MtDisabledLockGuard mtDisabler{v3MtDisabledLock()};

        // Read first filename
        v3Global.readFiles();
        v3Global.removeStd();
    }

    // Link, etc, if needed
    if (!v3Global.opt.preprocOnly()) {  //
        process();
    }

    // Final steps
    V3Global::dumpCheckGlobalTree("final", 990, dumpTreeEitherLevel() >= 3);
    if (v3Global.opt.jsonOnly()) {
        const string filename
            = (v3Global.opt.jsonOnlyMetaOutput().empty()
                   ? v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + ".tree.meta.json"
                   : v3Global.opt.jsonOnlyMetaOutput());
        v3Global.rootp()->dumpJsonMetaFile(filename);
    }

    V3Error::abortIfErrors();

    if (v3Global.opt.isWaiverOutput()) {
        // Create waiver output, must be just before we exit on warnings
        V3Waiver::write(v3Global.opt.waiverOutput());
    }

    V3Error::abortIfWarnings();

    if (v3Global.hierPlanp()) {  // This run is for just write a makefile
        const V3MtDisabledLockGuard mtDisabler{v3MtDisabledLock()};

        UASSERT(v3Global.opt.hierarchical(), "hierarchical must be set");
        UASSERT(!v3Global.opt.hierChild(), "This must not be a hierarchical-child run");
        UASSERT(v3Global.opt.hierBlocks().empty(), "hierarchical-block must not be set");
        if (v3Global.opt.gmake()) {
            v3Global.hierPlanp()->writeCommandArgsFiles(false);
            V3EmitMk::emitHierVerilation(v3Global.hierPlanp());
        }
        if (v3Global.opt.cmake()) {
            v3Global.hierPlanp()->writeCommandArgsFiles(true);
            V3EmitCMake::emit();
        }
    }
    if (v3Global.opt.makeDepend().isTrue()) {
        string filename = v3Global.opt.makeDir() + "/" + v3Global.opt.prefix();
        filename += v3Global.opt.hierTop() ? "__hierVer.d" : "__ver.d";
        V3File::writeDepend(filename);
    }
    if (v3Global.opt.protectIds()) {
        VIdProtect::writeMapFile(v3Global.opt.hierTopDataDir() + "/" + v3Global.opt.prefix()
                                 + "__idmap.xml");
    }

    if (v3Global.opt.skipIdentical().isTrue() || v3Global.opt.makeDepend().isTrue()) {
        V3File::writeTimes(v3Global.opt.hierTopDataDir() + "/" + v3Global.opt.prefix()
                               + "__verFiles.dat",
                           argString);
    }

    V3Os::filesystemFlushBuildDir(v3Global.opt.makeDir());
    if (v3Global.opt.hierTop()) V3Os::filesystemFlushBuildDir(v3Global.opt.hierTopDataDir());

    // Final writing shouldn't throw warnings, but...
    V3Error::abortIfWarnings();
}

static string buildMakeCmd(const string& makefile, const string& target) {
    const V3StringList& makeFlags = v3Global.opt.makeFlags();
    const int jobs = v3Global.opt.buildJobs();
    UASSERT(jobs >= 0, "-j option parser in V3Options.cpp filters out negative value");

    std::ostringstream cmd;
    cmd << v3Global.opt.getenvMAKE();
    cmd << " -C " << v3Global.opt.makeDir();
    cmd << " -f " << makefile;
    // Unless using make's jobserver, do a -j
    if (v3Global.opt.getenvMAKEFLAGS().find("-jobserver-auth") == string::npos) {
        if (jobs > 0) cmd << " -j " << jobs;
    }
    for (const string& flag : makeFlags) cmd << ' ' << flag;
    if (!target.empty()) cmd << ' ' << target;

    return cmd.str();
}

static void execBuildJob() {
    UASSERT(v3Global.opt.build(), "--build is not specified.");
    UASSERT(v3Global.opt.gmake(), "--build requires GNU Make.");
    UASSERT(!v3Global.opt.cmake(), "--build cannot use CMake.");
    UINFO(1, "Start Build\n");

    const string cmdStr = buildMakeCmd(v3Global.opt.prefix() + ".mk", "");
    V3Os::filesystemFlushBuildDir(v3Global.opt.hierTopDataDir());
    const int exit_code = V3Os::system(cmdStr);
    if (exit_code != 0) {
        v3error(cmdStr << " exited with " << exit_code << std::endl);
        std::exit(exit_code);
    }
}

static void execHierVerilation() {
    UASSERT(v3Global.hierPlanp(), "must be called only when plan exists");
    const string makefile = v3Global.opt.prefix() + "_hier.mk ";
    const string target = v3Global.opt.build() ? " hier_build" : " hier_verilation";
    const string cmdStr = buildMakeCmd(makefile, target);
    V3Os::filesystemFlushBuildDir(v3Global.opt.hierTopDataDir());
    const int exit_code = V3Os::system(cmdStr);
    if (exit_code != 0) {
        v3error(cmdStr << " exited with " << exit_code << std::endl);
        std::exit(exit_code);
    }
}

//######################################################################

int main(int argc, char** argv) {
    // General initialization
    std::ios::sync_with_stdio();

    time_t randseed;
    time(&randseed);
    srand(static_cast<int>(randseed));

    const string argString = V3Options::argString(argc - 1, argv + 1);
    {
        const V3MtDisabledLockGuard mtDisabler{v3MtDisabledLock()};

        // Post-constructor initialization of netlists
        v3Global.boot();

        // Preprocessor
        // Before command parsing so we can handle -Ds on command line.
        V3PreShell::boot();

        // Command option parsing
        v3Global.opt.buildDepBin(V3Os::filenameCleanup(argv[0]));
        v3Global.opt.parseOpts(new FileLine{FileLine::commandLineFilename()}, argc - 1, argv + 1);

        // Validate settings (aka Boost.Program_options)
        v3Global.opt.notify();
        v3Global.rootp()->timeInit();
    }

    V3Error::abortIfErrors();

    if (v3Global.opt.verilate()) {
        verilate(argString);
    } else {
        UINFO(1, "Option --no-verilate: Skip Verilation\n");
    }

    if (v3Global.hierPlanp() && v3Global.opt.gmake()) {
        execHierVerilation();  // execHierVerilation() takes care of --build too
    } else if (v3Global.opt.build()) {
        execBuildJob();
    }

    {
        const V3MtDisabledLockGuard mtDisabler{v3MtDisabledLock()};

        // Explicitly release resources
        V3PreShell::shutdown();
        v3Global.shutdown();
        FileLine::deleteAllRemaining();
    }

    UINFO(1, "Done, Exiting...\n");
}
