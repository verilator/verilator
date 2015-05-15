// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: main()
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "V3Global.h"
#include "V3Ast.h"
#include <ctime>
#include <sys/stat.h>

#include "V3Active.h"
#include "V3ActiveTop.h"
#include "V3Assert.h"
#include "V3AssertPre.h"
#include "V3Begin.h"
#include "V3Branch.h"
#include "V3Case.h"
#include "V3Cast.h"
#include "V3Changed.h"
#include "V3Clean.h"
#include "V3ClkGater.h"
#include "V3Clock.h"
#include "V3Combine.h"
#include "V3Const.h"
#include "V3Coverage.h"
#include "V3CoverageJoin.h"
#include "V3Dead.h"
#include "V3Delayed.h"
#include "V3Depth.h"
#include "V3DepthBlock.h"
#include "V3Descope.h"
#include "V3EmitC.h"
#include "V3EmitMk.h"
#include "V3EmitV.h"
#include "V3EmitXml.h"
#include "V3Expand.h"
#include "V3File.h"
#include "V3Cdc.h"
#include "V3Gate.h"
#include "V3GenClk.h"
#include "V3Graph.h"
#include "V3Inline.h"
#include "V3Inst.h"
#include "V3Life.h"
#include "V3LifePost.h"
#include "V3LinkCells.h"
#include "V3LinkDot.h"
#include "V3LinkJump.h"
#include "V3LinkLValue.h"
#include "V3LinkLevel.h"
#include "V3LinkParse.h"
#include "V3LinkResolve.h"
#include "V3Localize.h"
#include "V3Name.h"
#include "V3Order.h"
#include "V3Os.h"
#include "V3Param.h"
#include "V3Parse.h"
#include "V3ParseSym.h"
#include "V3PreShell.h"
#include "V3Premit.h"
#include "V3Scope.h"
#include "V3Slice.h"
#include "V3Split.h"
#include "V3SplitAs.h"
#include "V3Stats.h"
#include "V3Subst.h"
#include "V3Table.h"
#include "V3Task.h"
#include "V3Trace.h"
#include "V3TraceDecl.h"
#include "V3Tristate.h"
#include "V3Undriven.h"
#include "V3Unknown.h"
#include "V3Unroll.h"
#include "V3Width.h"

V3Global v3Global;

//######################################################################
// V3 Class -- top level

AstNetlist* V3Global::makeNetlist() {
    AstNetlist* newp = new AstNetlist();
    newp->addTypeTablep(new AstTypeTable(newp->fileline()));
    return newp;
}

void V3Global::checkTree() { rootp()->checkTree(); }

void V3Global::clear() {
    if (m_rootp) m_rootp->deleteTree(); m_rootp=NULL;
}

void V3Global::readFiles() {
    // NODE STATE
    //   AstNode::user4p()	// VSymEnt*    Package and typedef symbol names
    AstUser4InUse	inuser4;

    V3InFilter filter (v3Global.opt.pipeFilter());
    V3ParseSym parseSyms (v3Global.rootp());  // Symbol table must be common across all parsing

    V3Parse parser (v3Global.rootp(), &filter, &parseSyms);
    // Read top module
    const V3StringList& vFiles = v3Global.opt.vFiles();
    for (V3StringList::const_iterator it = vFiles.begin(); it != vFiles.end(); ++it) {
	string filename = *it;
	parser.parseFile(new FileLine("COMMAND_LINE",0), filename, false,
			 "Cannot find file containing module: ");
    }

    // Read libraries
    // To be compatible with other simulators,
    // this needs to be done after the top file is read
    const V3StringSet& libraryFiles = v3Global.opt.libraryFiles();
    for (V3StringSet::const_iterator it = libraryFiles.begin(); it != libraryFiles.end(); ++it) {
	string filename = *it;
	parser.parseFile(new FileLine("COMMAND_LINE",0), filename, true,
			 "Cannot find file containing library module: ");
    }
    //v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("parse.tree"));
    V3Error::abortIfErrors();

    if (!v3Global.opt.preprocOnly()) {
	// Resolve all modules cells refer to
	V3LinkCells::link(v3Global.rootp(), &filter, &parseSyms);
    }
}

void V3Global::dumpCheckGlobalTree(const string& filename, int newNumber, bool doDump) {
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename(filename, newNumber), false, doDump);
}

//######################################################################

void process () {
    // Sort modules by level so later algorithms don't need to care
    V3LinkLevel::modSortByLevel();
    V3Error::abortIfErrors();

    // Convert parseref's to varrefs, and other directly post parsing fixups
    V3LinkParse::linkParse(v3Global.rootp());
    // Cross-link signal names
    // Cross-link dotted hierarchical references
    V3LinkDot::linkDotPrimary(v3Global.rootp());
    v3Global.checkTree();  // Force a check, as link is most likely place for problems
    // Correct state we couldn't know at parse time, repair SEL's
    V3LinkResolve::linkResolve(v3Global.rootp());
    // Set Lvalue's in variable refs
    V3LinkLValue::linkLValue(v3Global.rootp());
    // Convert return/continue/disable to jumps
    V3LinkJump::linkJump(v3Global.rootp());
    V3Error::abortIfErrors();

    if (v3Global.opt.stats()) V3Stats::statsStageAll(v3Global.rootp(), "Link");

    // Remove parameters by cloning modules to de-parameterized versions
    //   This requires some width calculations and constant propagation
    V3Param::param(v3Global.rootp());
    V3LinkDot::linkDotParamed(v3Global.rootp());	// Cleanup as made new modules
    V3Error::abortIfErrors();

    // Remove any modules that were parameterized and are no longer referenced.
    V3Dead::deadifyModules(v3Global.rootp());
    v3Global.checkTree();

    // Calculate and check widths, edit tree to TRUNC/EXTRACT any width mismatches
    V3Width::width(v3Global.rootp());

    V3Error::abortIfErrors();

    // Commit to the widths we've chosen; Make widthMin==width
    V3Width::widthCommit(v3Global.rootp());
    v3Global.assertDTypesResolved(true);
    v3Global.widthMinUsage(VWidthMinUsage::MATCHES_WIDTH);

    // Coverage insertion
    //    Before we do dead code elimination and inlining, or we'll lose it.
    if (v3Global.opt.coverage()) {
	V3Coverage::coverage(v3Global.rootp());
    }

    // Push constants, but only true constants preserving liveness
    // so V3Undriven sees variables to be eliminated, ie "if (0 && foo) ..."
    V3Const::constifyAllLive(v3Global.rootp());

    // Signal based lint checks, no change to structures
    // Must be before first constification pass drops dead code
    V3Undriven::undrivenAll(v3Global.rootp());

    // Assertion insertion
    //    After we've added block coverage, but before other nasty transforms
    V3AssertPre::assertPreAll(v3Global.rootp());
    //
    V3Assert::assertAll(v3Global.rootp());

    if (!v3Global.opt.xmlOnly()) {
	// Add top level wrapper with instance pointing to old top
	// Move packages to under new top
	// Must do this after we know parameters and dtypes (as don't clone dtype decls)
	V3LinkLevel::wrapTop(v3Global.rootp());
    }

    // Propagate constants into expressions
    V3Const::constifyAllLint(v3Global.rootp());

    if (!v3Global.opt.xmlOnly()) {
	// Remove cell arrays (must be between V3Width and scoping)
	V3Inst::dearrayAll(v3Global.rootp());
    }

    if (!v3Global.opt.xmlOnly()) {
	// Expand inouts, stage 2
	// Also simplify pin connections to always be AssignWs in prep for V3Unknown
	V3Tristate::tristateAll(v3Global.rootp());

	// Task inlining & pushing BEGINs names to variables/cells
	// Begin processing must be after Param, before module inlining
	V3Begin::debeginAll(v3Global.rootp());	// Flatten cell names, before inliner

	// Move assignments from X into MODULE temps.
	// (Before flattening, so each new X variable is shared between all scopes of that module.)
	V3Unknown::unknownAll(v3Global.rootp());
	v3Global.constRemoveXs(true);

	// Module inlining
	// Cannot remove dead variables after this, as alias information for final
	// V3Scope's V3LinkDot is in the AstVar.
	if (v3Global.opt.oInline()) {
	    V3Inline::inlineAll(v3Global.rootp());
	    V3LinkDot::linkDotArrayed(v3Global.rootp());	// Cleanup as made new modules
	}
    }

    //--PRE-FLAT OPTIMIZATIONS------------------

    // Initial const/dead to reduce work for ordering code
    V3Const::constifyAll(v3Global.rootp());
    v3Global.checkTree();

    V3Dead::deadifyDTypes(v3Global.rootp());
    v3Global.checkTree();

    V3Error::abortIfErrors();

    //--FLATTENING---------------

    if (!v3Global.opt.xmlOnly()) {
	// We're going to flatten the hierarchy, so as many optimizations that
	// can be done as possible should be before this....

	// Convert instantiations to wassigns and always blocks
	V3Inst::instAll(v3Global.rootp());

	// Inst may have made lots of concats; fix them
	V3Const::constifyAll(v3Global.rootp());

	// Flatten hierarchy, creating a SCOPE for each module's usage as a cell
	V3Scope::scopeAll(v3Global.rootp());
	V3LinkDot::linkDotScope(v3Global.rootp());
    }

    //--SCOPE BASED OPTIMIZATIONS--------------

    if (!v3Global.opt.xmlOnly()) {
	// Cleanup
	V3Const::constifyAll(v3Global.rootp());
	V3Dead::deadifyDTypes(v3Global.rootp());
	v3Global.checkTree();

	// Convert case statements to if() blocks.  Must be after V3Unknown
	// Must be before V3Task so don't need to deal with task in case value compares
	V3Case::caseAll(v3Global.rootp());

	// Inline all tasks
	V3Task::taskAll(v3Global.rootp());

	// Add __PVT's
	// After V3Task so task internal variables will get renamed
	V3Name::nameAll(v3Global.rootp());

	// Loop unrolling & convert FORs to WHILEs
	V3Unroll::unrollAll(v3Global.rootp());

	// Expand slices of arrays
	V3Slice::sliceAll(v3Global.rootp());

	// Push constants across variables and remove redundant assignments
	V3Const::constifyAll(v3Global.rootp());

	if (v3Global.opt.oLife()) {
	    V3Life::lifeAll(v3Global.rootp());
	}

	// Make large low-fanin logic blocks into lookup tables
	// This should probably be done much later, once we have common logic elimination.
	if (!v3Global.opt.lintOnly() && v3Global.opt.oTable()) {
	    V3Table::tableAll(v3Global.rootp());
	}

	// Cleanup
	V3Const::constifyAll(v3Global.rootp());
	V3Dead::deadifyDTypes(v3Global.rootp());
	v3Global.checkTree();

	// Detect clock enables and mode into sensitives, and split always based on clocks
	// (so this is a good prelude to splitAlways.)
	if (v3Global.opt.oFlopGater()) {
	    V3ClkGater::clkGaterAll(v3Global.rootp());
	}

	// Move assignments/sensitives into a SBLOCK for each unique sensitivity list
	// (May convert some ALWAYS to combo blocks, so should be before V3Gate step.)
	V3Active::activeAll(v3Global.rootp());

	// Split single ALWAYS blocks into multiple blocks for better ordering chances
	if (v3Global.opt.oSplit()) {
	    V3Split::splitAlwaysAll(v3Global.rootp());
	}
	V3SplitAs::splitAsAll(v3Global.rootp());

	// Create tracing sample points, before we start eliminating signals
	if (v3Global.opt.trace()) {
	    V3TraceDecl::traceDeclAll(v3Global.rootp());
	}

	// Gate-based logic elimination; eliminate signals and push constant across cell boundaries
	// Instant propagation makes lots-o-constant reduction possibilities.
	if (v3Global.opt.oGate()) {
	    V3Gate::gateAll(v3Global.rootp());
	    // V3Gate calls constant propagation itself.
	} else {
	    v3info("Command Line disabled gate optimization with -Og/-O0.  This may cause ordering problems.");
	}

	// Combine COVERINCs with duplicate terms
	if (v3Global.opt.coverage()) {
	    V3CoverageJoin::coverageJoin(v3Global.rootp());
	}

	// Remove unused vars
	V3Const::constifyAll(v3Global.rootp());
	V3Dead::deadifyAll(v3Global.rootp());

	// Clock domain crossing analysis
	if (v3Global.opt.cdc()) {
	    V3Cdc::cdcAll(v3Global.rootp());
	    V3Error::abortIfErrors();
	    return;
	}

	// Reorder assignments in pipelined blocks
	if (v3Global.opt.oReorder()) {
	    V3Split::splitReorderAll(v3Global.rootp());
	}

	// Create delayed assignments
	// This creates lots of duplicate ACTIVES so ActiveTop needs to be after this step
	V3Delayed::delayedAll(v3Global.rootp());

	// Make Active's on the top level
	// Differs from V3Active, because identical clocks may be pushed down to a module and now be identical
	V3ActiveTop::activeTopAll(v3Global.rootp());

	if (v3Global.opt.stats()) V3Stats::statsStageAll(v3Global.rootp(), "PreOrder");

	// Order the code; form SBLOCKs and BLOCKCALLs
	V3Order::orderAll(v3Global.rootp());

	// Change generated clocks to look at delayed signals
	V3GenClk::genClkAll(v3Global.rootp());

	// Convert sense lists into IF statements.
	V3Clock::clockAll(v3Global.rootp());

	// Cleanup any dly vars or other temps that are simple assignments
	// Life must be done before Subst, as it assumes each CFunc under _eval is called only once.
	if (v3Global.opt.oLife()) {
	    V3Const::constifyAll(v3Global.rootp());
	    V3Life::lifeAll(v3Global.rootp());
	}
	if (v3Global.opt.oLifePost()) {
	    V3LifePost::lifepostAll(v3Global.rootp());
	}

	// Remove unused vars
	V3Const::constifyAll(v3Global.rootp());
	V3Dead::deadifyAll(v3Global.rootp());

	// Detect change loop
	V3Changed::changedAll(v3Global.rootp());

	// Create tracing logic, since we ripped out some signals the user might want to trace
	// Note past this point, we presume traced variables won't move between CFuncs
	// (It's OK if untraced temporaries move around, or vars "effectively" activate the same way.)
	if (v3Global.opt.trace()) {
	    V3Trace::traceAll(v3Global.rootp());
	}

	if (v3Global.opt.stats()) V3Stats::statsStageAll(v3Global.rootp(), "Scoped");

	// Remove scopes; make varrefs/funccalls relative to current module
	V3Descope::descopeAll(v3Global.rootp());
    }

    //--MODULE OPTIMIZATIONS--------------

    if (!v3Global.opt.xmlOnly()) {
	// Split deep blocks to appease MSVC++.  Must be before Localize.
	if (!v3Global.opt.lintOnly() && v3Global.opt.compLimitBlocks()) {
	    V3DepthBlock::depthBlockAll(v3Global.rootp());
	}

	// Move BLOCKTEMPS from class to local variables
	if (v3Global.opt.oLocalize()) {
	    V3Localize::localizeAll(v3Global.rootp());
	}

	// Icache packing; combine common code in each module's functions into subroutines
	if (v3Global.opt.oCombine()) {
	    V3Combine::combineAll(v3Global.rootp());
	}
    }

    V3Error::abortIfErrors();

    //--GENERATION------------------

    if (!v3Global.opt.xmlOnly()) {
	// Remove unused vars
	V3Const::constifyAll(v3Global.rootp());
	V3Dead::deadifyAll(v3Global.rootp());

	// Here down, widthMin() is the Verilog width, and width() is the C++ width
	// Bits between widthMin() and width() are irrelevant, but may be non zero.
	v3Global.widthMinUsage(VWidthMinUsage::VERILOG_WIDTH);

	// Make all math operations either 8, 16, 32 or 64 bits
	V3Clean::cleanAll(v3Global.rootp());

	// Move wide constants to BLOCK temps.
	V3Premit::premitAll(v3Global.rootp());
    }

    // Expand macros and wide operators into C++ primitives
    if (!v3Global.opt.xmlOnly()
	&& v3Global.opt.oExpand()) {
	V3Expand::expandAll(v3Global.rootp());
    }

    // Propagate constants across WORDSEL arrayed temporaries
    if (!v3Global.opt.xmlOnly()
	&& v3Global.opt.oSubst()) {
	// Constant folding of expanded stuff
	V3Const::constifyCpp(v3Global.rootp());
	V3Subst::substituteAll(v3Global.rootp());
    }
    if (!v3Global.opt.xmlOnly()
	&& v3Global.opt.oSubstConst()) {
	// Constant folding of substitutions
	V3Const::constifyCpp(v3Global.rootp());

	V3Dead::deadifyAll(v3Global.rootp());
    }

    if (!v3Global.opt.lintOnly()
	&& !v3Global.opt.xmlOnly()) {
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

    // Output the text
    if (!v3Global.opt.lintOnly()
	&& !v3Global.opt.xmlOnly()) {
	// emitcInlines is first, as it may set needHInlines which other emitters read
	V3EmitC::emitcInlines();
	V3EmitC::emitcSyms();
	V3EmitC::emitcTrace();
    }
    if (!v3Global.opt.xmlOnly()) { // Unfortunately we have some lint checks in emitc.
	V3EmitC::emitc();
    }
    if (v3Global.opt.xmlOnly()
	// Check XML when debugging to make sure no missing node types
	|| (v3Global.opt.debugCheck() && !v3Global.opt.lintOnly())) {
	V3EmitXml::emitxml();
    }

    // Statistics
    if (v3Global.opt.stats()) {
	V3Stats::statsFinalAll(v3Global.rootp());
	V3Stats::statsReport();
    }

    if (!v3Global.opt.lintOnly()
	&& !v3Global.opt.xmlOnly()) {
	// Makefile must be after all other emitters
	V3EmitMk::emitmk(v3Global.rootp());
    }

    // Note early return above when opt.cdc()
}

//######################################################################

int main(int argc, char** argv, char** env) {
    // General initialization
    ios::sync_with_stdio();

    time_t randseed;
    time(&randseed);
    srand( (int) randseed);

    // Post-constructor initialization of netlists
    v3Global.boot();

    // Preprocessor
    // Before command parsing so we can handle -Ds on command line.
    V3PreShell::boot(env);

    // Command option parsing
    v3Global.opt.bin(argv[0]);
    string argString = V3Options::argString(argc-1, argv+1);
    v3Global.opt.parseOpts(new FileLine("COMMAND_LINE",0), argc-1, argv+1);
    if (!v3Global.opt.outFormatOk()
	&& !v3Global.opt.preprocOnly()
	&& !v3Global.opt.lintOnly()
	&& !v3Global.opt.xmlOnly()
	&& !v3Global.opt.cdc()) {
	v3fatal("verilator: Need --cc, --sc, --cdc, --lint-only, --xml_only or --E option");
    }
    // Check environment
    V3Options::getenvSYSTEMC();
    V3Options::getenvSYSTEMC_ARCH();
    V3Options::getenvSYSTEMC_INCLUDE();
    V3Options::getenvSYSTEMC_LIBDIR();
    V3Options::getenvSYSTEMPERL();
    V3Options::getenvSYSTEMPERL_INCLUDE();

    V3Error::abortIfErrors();

    // Can we skip doing everything if times are ok?
    V3File::addSrcDepend(v3Global.opt.bin());
    if (v3Global.opt.skipIdentical()
	&& !v3Global.opt.preprocOnly()
	&& !v3Global.opt.lintOnly()
	&& !v3Global.opt.cdc()
	&& V3File::checkTimes(v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"__verFiles.dat", argString)) {
	UINFO(1,"--skip-identical: No change to any source files, exiting\n");
	exit(0);
    }

    // Internal tests (after option parsing as need debug() setting)
    AstBasicDTypeKwd::test();
    V3Graph::test();

    //--FRONTEND------------------

    // Cleanup
    V3Os::unlinkRegexp(v3Global.opt.makeDir(), v3Global.opt.prefix()+"_*.tree");
    V3Os::unlinkRegexp(v3Global.opt.makeDir(), v3Global.opt.prefix()+"_*.dot");
    V3Os::unlinkRegexp(v3Global.opt.makeDir(), v3Global.opt.prefix()+"_*.txt");

    // Read first filename
    v3Global.readFiles();

    // Link, etc, if needed
    if (!v3Global.opt.preprocOnly()) {
	process();
    }

    // Final steps
    V3Global::dumpCheckGlobalTree("final.tree", 990, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
    V3Error::abortIfWarnings();

    if (!v3Global.opt.lintOnly() && !v3Global.opt.cdc()
	&& v3Global.opt.makeDepend()) {
	V3File::writeDepend(v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"__ver.d");
    }
    if (!v3Global.opt.lintOnly() && !v3Global.opt.cdc()
	&& (v3Global.opt.skipIdentical() || v3Global.opt.makeDepend())) {
	V3File::writeTimes(v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"__verFiles.dat", argString);
    }

    // Final writing shouldn't throw warnings, but...
    V3Error::abortIfWarnings();
#ifdef VL_LEAK_CHECKS
    // Cleanup memory for valgrind leak analysis
    v3Global.clear();
#endif
    FileLine::deleteAllRemaining();

    UINFO(1,"Done, Exiting...\n");
}
