// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: main()
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2006 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "V3Global.h"
#include "V3Ast.h"
#include <time.h>
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
#include "V3Clock.h"
#include "V3Combine.h"
#include "V3Const.h"
#include "V3Coverage.h"
#include "V3Dead.h"
#include "V3Delayed.h"
#include "V3Depth.h"
#include "V3Descope.h"
#include "V3EmitC.h"
#include "V3EmitMk.h"
#include "V3EmitV.h"
#include "V3Expand.h"
#include "V3File.h"
#include "V3Gate.h"
#include "V3Graph.h"
#include "V3GenClk.h"
#include "V3Inline.h"
#include "V3Inst.h"
#include "V3Life.h"
#include "V3LifePost.h"
#include "V3Link.h"
#include "V3LinkCells.h"
#include "V3LinkDot.h"
#include "V3LinkLevel.h"
#include "V3LinkResolve.h"
#include "V3Localize.h"
#include "V3Name.h"
#include "V3Order.h"
#include "V3Param.h"
#include "V3PreShell.h"
#include "V3Premit.h"
#include "V3Read.h"
#include "V3Scope.h"
#include "V3Signed.h"
#include "V3Split.h"
#include "V3Stats.h"
#include "V3Subst.h"
#include "V3Table.h"
#include "V3Task.h"
#include "V3Trace.h"
#include "V3TraceDecl.h"
#include "V3Unknown.h"
#include "V3Unroll.h"
#include "V3Width.h"

V3Global v3Global;

//######################################################################
// V3 Class -- top level

void V3Global::readFiles() {
    V3Read reader (m_rootp);
    // Read libraries
    for (V3StringSet::iterator it = v3Global.opt.libraryFiles().begin();
	 it != v3Global.opt.libraryFiles().end(); ++it) {
	string filename = *it;
	reader.readFile(new FileLine("CommandLine",0), filename, true);
    }
    // Read top module
    reader.readFile(new FileLine("CommandLine",0), opt.top(), false);
    V3Error::abortIfErrors();
}

//######################################################################

void process () {
    // Resolve all modules cells refer to
    V3LinkCells::link(v3Global.rootp());
    V3LinkLevel::modSortByLevel();
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("cells.tree"));
    V3Error::abortIfErrors();

    // Cross-link signal names
    V3Link::link(v3Global.rootp());
    // Cross-link dotted hierarchical references
    V3LinkDot::linkDot(v3Global.rootp());
    // Correct state we couldn't know at parse time, repair SEL's, set lvalue's
    V3LinkResolve::linkResolve(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("link.tree"));
    V3Error::abortIfErrors();

    if (v3Global.opt.stats()) V3Stats::statsStageAll(v3Global.rootp(), "Link");

    // Remove parameters by cloning modules to de-parameterized versions
    //   This requires some width calculations and constant propagation
    V3Param::param(v3Global.rootp());
    V3LinkDot::linkDot(v3Global.rootp());	// Cleanup as made new modules
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("param.tree"));
    V3Error::abortIfErrors();

    // Remove any modules that were parameterized and are no longer referenced.
    V3Dead::deadifyAll(v3Global.rootp(), false);
    //v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("dead.tree"));
    v3Global.checkTree();

    // Calculate and check widths, edit tree to TRUNC/EXTRACT any width mismatches
    V3Width::width(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("width.tree"));

    // Compute signed/unsigned
    V3Signed::signedAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("signed.tree"));
    V3Error::abortIfErrors();

    // Commit to the widths we've chosen; Make widthMin==width
    V3Width::widthCommit(v3Global.rootp());
    v3Global.assertWidthsSame(true);
    //v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("widthcommit.tree"));

    // Coverage insertion
    //    Before we do dead code elimination and inlining, or we'll loose it.
    if (v3Global.opt.coverage()) {
	V3Coverage::coverage(v3Global.rootp());
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("coverage.tree"));
    }

    // Assertion insertion
    //    After we've added block coverage, but before other nasty transforms
    if (v3Global.opt.assertOn() || v3Global.opt.psl()) {
	V3AssertPre::assertPreAll(v3Global.rootp());
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("assertpre.tree"));
	//
	V3Assert::assertAll(v3Global.rootp());
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("assert.tree"));
    }

    // Add top level wrapper with instance pointing to old top
    // Must do this after we know the width of any parameters
    // We also do it after coverage/assertion insertion so we don't 'cover' the top level.
    V3LinkLevel::wrapTop(v3Global.rootp());

    // Propagate constants into expressions
    V3Const::constifyAllLint(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("const.tree"));

    // Remove cell arrays (must be between V3Width and tasking)
    V3Inst::dearrayAll(v3Global.rootp());
    //v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("dearray.tree"));

    // Move assignments from X into MODULE temps.
    // (Before flattening, so each new X variable is shared between all scopes of that module.)
    V3Unknown::unknownAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("unknown.tree"));

    // Task inlining & pushing BEGINs names to variables/cells
    // Begin processing must be after Param, before module inlining
    V3Begin::debeginAll(v3Global.rootp());	// Flatten cell names, before inliner
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("begin.tree"));

    // Module inlining
    // Cannot remove dead variables after this, as alias information for final
    // V3Scope's V3LinkDot is in the AstVar.
    if (v3Global.opt.oInline()) {
	V3Inline::inlineAll(v3Global.rootp());
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("inline.tree"));
	V3LinkDot::linkDot(v3Global.rootp());	// Cleanup as made new modules
	//v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("linkdot.tree"));
    }

    //--PRE-FLAT OPTIMIZATIONS------------------

    // Initial const/dead to reduce work for ordering code
    V3Const::constifyAll(v3Global.rootp());
    v3Global.checkTree();
    V3Dead::deadifyAll(v3Global.rootp(), false);
    v3Global.checkTree();
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("const.tree"));

    V3Error::abortIfErrors();

    //--FLATTENING---------------

    // We're going to flatten the hierarchy, so as many optimizations that
    // can be done as possible should be before this....

    // Convert instantiations to wassigns and always blocks
    V3Inst::instAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("inst.tree"));

    // Inst may have made lots of concats; fix them
    V3Const::constifyAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("const.tree"));

    // Flatten hierarchy, creating a SCOPE for each module's usage as a cell
    V3Scope::scopeAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("scope.tree"));
    V3LinkDot::linkDotScope(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("linkdot.tree"));
    
    //--SCOPE BASED OPTIMIZATIONS--------------

    // Cleanup
    V3Const::constifyAll(v3Global.rootp());
    V3Dead::deadifyAll(v3Global.rootp(), false);
    v3Global.checkTree();
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("const.tree"));

    // Inline all tasks
    V3Task::taskAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("task.tree"));

    // Add __PVT's
    // After V3Task so task internal variables will get renamed
    V3Name::nameAll(v3Global.rootp());
    //v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("name.tree"));

    // Loop unrolling & convert FORs to WHILEs
    V3Unroll::unrollAll(v3Global.rootp());
    //v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("unroll.tree"));

    // Convert case statements to if() blocks.  Must be after V3Unknown
    V3Case::caseAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("case.tree"));

    V3Const::constifyAll(v3Global.rootp());
    //v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("const.tree"));

    // Make large low-fanin logic blocks into lookup tables
    // This should probably be done much later, once we have common logic elimination.
    if (v3Global.opt.oTable()) {
	V3Table::tableAll(v3Global.rootp());
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("table.tree"));
    }

    // Cleanup
    V3Const::constifyAll(v3Global.rootp());
    V3Dead::deadifyAll(v3Global.rootp(), false);
    v3Global.checkTree();
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("const.tree"));

    // Move assignments/sensitives into a SBLOCK for each unique sensitivity list
    // (May convert some ALWAYS to combo blocks, so should be before V3Gate step.)
    V3Active::activeAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("active.tree"));

    // Split single ALWAYS blocks into multiple blocks for better ordering chances
    if (v3Global.opt.oSplit()) {
	V3Split::splitAlwaysAll(v3Global.rootp());
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("split.tree"));
    }

    // Create tracing sample points, before we start eliminating signals
    if (v3Global.opt.trace()) {
	V3TraceDecl::traceDeclAll(v3Global.rootp());
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("tracedecl.tree"));
    }

    // Gate-based logic elimination; eliminate signals and push constant across cell boundaries
    // Instant propagation makes lots-o-constant reduction possibilities.
    if (v3Global.opt.oGate()) {
	V3Gate::gateAll(v3Global.rootp());
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("gate.tree"));
    }

    // Reorder assignments in pipelined blocks
    if (v3Global.opt.oReorder()) {
	V3Split::splitReorderAll(v3Global.rootp());
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("reorder.tree"));
    }

    // Create delayed assignments
    // This creates lots of duplicate ACTIVES so ActiveTop needs to be after this step
    V3Delayed::delayedAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("delayed.tree"));

    // Make Active's on the top level
    // Differs from V3Active, because identical clocks may be pushed down to a module and now be identical
    V3ActiveTop::activeTopAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("activetop.tree"));

    if (v3Global.opt.stats()) V3Stats::statsStageAll(v3Global.rootp(), "PreOrder");

    // Order the code; form SBLOCKs and BLOCKCALLs
    V3Order::orderAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("order.tree"));

#ifndef NEW_ORDERING
    // Change generated clocks to look at delayed signals
    V3GenClk::genClkAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("genclk.tree"));
#endif

    // Convert sense lists into IF statements.
    V3Clock::clockAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("clock.tree"));

    // Cleanup any dly vars or other temps that are simple assignments
    if (v3Global.opt.oLife()) {
	V3Life::lifeAll(v3Global.rootp());
    }
    if (v3Global.opt.oLifePost()) {
	V3LifePost::lifepostAll(v3Global.rootp());
    }
    if (v3Global.opt.oLife() || v3Global.opt.oLifePost()) {
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("life.tree"));
    }

    // Remove unused vars
    V3Const::constifyAll(v3Global.rootp());
    V3Dead::deadifyAll(v3Global.rootp(), false);
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("const.tree"));

#ifndef NEW_ORDERING
    // Detect change loop
    V3Changed::changedAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("changed.tree"));
#endif

    // Create tracing logic, since we ripped out some signals the user might want to trace
    // Note past this point, we presume traced variables won't move between CFuncs
    // (It's OK if untraced temporaries move around, or vars "effectively" activate the same way.)
    if (v3Global.opt.trace()) {
	V3Trace::traceAll(v3Global.rootp());
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("trace.tree"));
    }

    if (v3Global.opt.stats()) V3Stats::statsStageAll(v3Global.rootp(), "Scoped");

    // Remove scopes; make varrefs/funccalls relative to current module
    V3Descope::descopeAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("descope.tree"));

    //--MODULE OPTIMIZATIONS--------------

    // Move BLOCKTEMPS from class to local variables
    if (v3Global.opt.oLocalize()) {
	V3Localize::localizeAll(v3Global.rootp());
    }

    // Icache packing; combine common code in each module's functions into subroutines
    if (v3Global.opt.oCombine()) {
	V3Combine::combineAll(v3Global.rootp());
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("combine.tree"));
    }

    V3Error::abortIfErrors();

    //--GENERATION------------------

    // Remove unused vars
    V3Const::constifyAll(v3Global.rootp());
    V3Dead::deadifyAll(v3Global.rootp(), true);
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("const.tree"));

    // Here down, widthMin() is the Verilog width, and width() is the C++ width
    // Bits between widthMin() and width() are irrelevant, but may be non zero.
    v3Global.assertWidthsSame(false);

    // Make all operations a multiple of 32 bits
    V3Clean::cleanAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("clean.tree"));

    // Move wide constants to BLOCK temps.
    V3Premit::premitAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("premit.tree"));

    // Expand macros and wide operators into C++ primitives
    if (v3Global.opt.oExpand()) {
	V3Expand::expandAll(v3Global.rootp());
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("expand.tree"));
    }

    // Propagate constants across WORDSEL arrayed temporaries
    if (v3Global.opt.oSubst()) {
	// Constant folding of expanded stuff
	V3Const::constifyCpp(v3Global.rootp());
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("const.tree"));
	V3Subst::substituteAll(v3Global.rootp());
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("subst.tree"));
    }
    if (v3Global.opt.oSubstConst()) {
	// Constant folding of substitutions
	V3Const::constifyCpp(v3Global.rootp());

	V3Dead::deadifyAll(v3Global.rootp(), true);
	v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("dead.tree"));
    }

    // Fix very deep expressions
    // Mark evaluation functions as member functions, if needed.
    V3Depth::depthAll(v3Global.rootp());
    //v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("depth.tree"));

    // Branch prediction
    V3Branch::branchAll(v3Global.rootp());

    // Add C casts when longs need to become long-long and vice-versa
    // Note depth may insert something needing a cast, so this must be last.
    V3Cast::castAll(v3Global.rootp());
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("cast.tree"));

    V3Error::abortIfErrors();

    // Output the text
    V3EmitC::emitcSyms();
    V3EmitC::emitcTrace();
    V3EmitC::emitc();

    // Statistics
    if (v3Global.opt.stats()) {
	V3Stats::statsFinalAll(v3Global.rootp());
	V3Stats::statsReport();
    }

    // Makefile must be after all other emitters
    V3EmitMk::emitmk(v3Global.rootp());
}

//######################################################################

int main(int argc, char** argv, char** env) {
    // General initialization
    ios::sync_with_stdio();

    time_t randseed;
    time(&randseed);
    srand( (int) randseed);

    // Preprocessor
    V3PreShell::boot(env);

    // Command option parsing
    string argString = V3Options::argString(argc-1, argv+1);
    v3Global.opt.parseOpts(new FileLine("COMMAND_LINE",0), argc-1, argv+1);
    if (v3Global.opt.coverage() && !v3Global.opt.systemPerl()) {
	v3fatal("Unsupported: Coverage analysis requires --sp output.");
    }
    if (!v3Global.opt.outFormatOk() && !v3Global.opt.preprocOnly()) {
	v3fatal("verilator: Need --cc, --sc, --sp or --E option");
    }

    V3Error::abortIfErrors();

    // Can we skip doing everything if times are ok?
    V3File::addSrcDepend(v3Global.opt.bin());
    if (v3Global.opt.skipIdentical()
	&& !v3Global.opt.preprocOnly()
	&& V3File::checkTimes(v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"__verFiles.dat", argString)) {
	UINFO(1,"--skip-identical: No change to any source files, exiting\n");
	exit(0);
    }

    // Internal tests (after option parsing as need debug() setting)
    V3Graph::test();

    //--FRONTEND------------------

    // Cleanup
    mkdir(v3Global.opt.makeDir().c_str(), 0777);
    string cleanFilename = "/bin/rm -rf "+v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"_*.tree";
    system(cleanFilename.c_str());
    cleanFilename = "/bin/rm -rf "+v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"_*.dot";
    system(cleanFilename.c_str());
    cleanFilename = "/bin/rm -rf "+v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"_*.txt";
    system(cleanFilename.c_str());

    // Read first filename
    v3Global.readFiles();
    //v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("parse.tree"));

    // Link, etc, if needed
    if (!v3Global.opt.preprocOnly()) {
	process();
    }

    // Final steps
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("final.tree",99));
    V3Error::abortIfErrors();

    if (v3Global.opt.makeDepend()) {
	V3File::writeDepend(v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"__ver.d");
    }
    if (v3Global.opt.skipIdentical() || v3Global.opt.makeDepend()) { 
	V3File::writeTimes(v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"__verFiles.dat", argString);
    }

#ifdef VL_LEAK_CHECKS
    // Cleanup memory for valgrind leak analysis
    v3Global.clear();
#endif
    
    UINFO(1,"Done, Exiting...\n");
}
