// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// VlCovInstHandle properties no SystemVerilog covergroup can produce.
//
//  1. An attach count above 1.  The handle's copy constructor is reached only
//     through a generated clone(), i.e. 'cg c2 = new c1;' -- a construct
//     Verilator is slated to reject.  Testing attach counting through it would
//     mean a test whose reason to exist is scheduled for removal, so the count
//     is exercised directly here.  The copy constructor must still compile:
//     every generated class clone()s its members.
//
//  2. A handle outliving the registry.  Examples declare the context before the
//     model, so the registry is alive when the last handle drops; this is the
//     other order.  Handle destructors reach into the registry, so
//     ~VlCovRegistry cannot free the nodes -- that would turn a harmless usage
//     error into a use-after-free on the node.  It leaks attached types instead.
//
// The model makes case 2 realistic and is deliberately never deleted: deleting
// it after the context runs ~VerilatedSyms, whose checkMagic() on the freed
// context is a pre-existing runtime use-after-free unrelated to covergroups.
//
// Run under -fsanitize=address; both cases fail as use-after-free.

#include <verilated.h>
#include <verilated_covergroup.h>

#include VM_PREFIX_INCLUDE

#include <cstdio>

double sc_time_stamp() { return 0; }

int errors = 0;

void checkEq(const char* what, uint32_t got, uint32_t exp) {
    if (got != exp) {
        printf("%%Error: %s: got=%u exp=%u\n", what, got, exp);
        ++errors;
    }
}

int main(int argc, char* argv[]) {
    VerilatedContext* const contextp = new VerilatedContext;
    contextp->commandArgs(argc, argv);

    VM_PREFIX* const topp = new VM_PREFIX{contextp, "top"};

    VlCovRegistry* const registryp = contextp->covergroupRegistryp();

    {
        // ---- Case 1: attach count above 1 ----
        VlCovInstHandle first;
        first.attach(registryp->newCovergroupInst("cg_handle"));
        checkEq("one handle, one node", registryp->liveInstanceCount("cg_handle"), 1);
        checkEq("nothing retired yet", registryp->retiredInstanceCount("cg_handle"), 0);

        {
            // Copy-construction shares the node; it does not make a second one.
            const VlCovInstHandle second{first};  // NOLINT: exercising the copy ctor
            checkEq("copy shares the node", registryp->liveInstanceCount("cg_handle"), 1);
            checkEq("copy created nothing", registryp->createdInstanceCount("cg_handle"), 1);
        }
        // 'second' is gone, 'first' is not.  The node must still be here: an
        // attach count that never rose would have retired it on that drop, and
        // the queries below would then be reading freed storage.
        checkEq("node outlives the copy", registryp->liveInstanceCount("cg_handle"), 1);
        checkEq("nothing retired on the copy", registryp->retiredInstanceCount("cg_handle"), 0);

        // ---- Case 2: a handle outliving the registry ----
        // Give the design its covergroup instance first, so the registry has a
        // second attached type when it is destroyed.
        for (int i = 0; i < 8; ++i) {
            topp->clk = i & 1;
            topp->eval();
            contextp->timeInc(1);
        }

        delete contextp;  // NOLINT: the wrong destruction order is the point

        // ~first runs at the end of this block: attachDec() on a node whose
        // registry is already gone.  Nothing may query the registry from here on
        // -- it no longer exists -- so the check is simply that this is not a
        // use-after-free.
    }

    // topp is deliberately leaked; see the header comment.
    (void)topp;

    if (errors) {
        printf("%%Error: %d failure(s)\n", errors);
        return 10;
    }
    printf("*-* All Finished *-*\n");
    return 0;
}
