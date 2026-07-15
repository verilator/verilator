// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: $finish source propagation with a user callback
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0
//
//*************************************************************************

#include "verilated.h"

#include "Vt_finish_public.h"
#include "Vt_finish_public_public_top.h"

#include <cstdio>

namespace {
unsigned s_finishCount = 0;
}

void vl_finish(const char*, int, const char*) VL_MT_UNSAFE { ++s_finishCount; }

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    Vt_finish_public top{&context};

    const uint32_t result = top.public_top->public_finish();
    if (s_finishCount != 1 || result != 0 || top.public_top->public_after != 0) {
        std::fprintf(stderr, "%%Error: public finish count=%u result=%u after=%u exp=1,0,0\n",
                     s_finishCount, static_cast<unsigned>(result),
                     static_cast<unsigned>(top.public_top->public_after));
        return 1;
    }
    if (context.gotFinish()) {
        std::fprintf(stderr, "%%Error: public finish latched gotFinish\n");
        return 1;
    }

    const uint32_t staticPrime = top.public_top->public_static_finish(false);
    if (s_finishCount != 1 || staticPrime != 123 || top.public_top->static_public_after != 1) {
        std::fprintf(stderr,
                     "%%Error: static public prime count=%u result=%u after=%u exp=1,123,1\n",
                     s_finishCount, static_cast<unsigned>(staticPrime),
                     static_cast<unsigned>(top.public_top->static_public_after));
        return 1;
    }
    const uint32_t staticResult = top.public_top->public_static_finish(true);
    if (s_finishCount != 2 || staticResult != 0 || top.public_top->static_public_after != 1) {
        std::fprintf(stderr,
                     "%%Error: static public finish count=%u result=%u after=%u exp=2,0,1\n",
                     s_finishCount, static_cast<unsigned>(staticResult),
                     static_cast<unsigned>(top.public_top->static_public_after));
        return 1;
    }
    top.public_top->property_finish = true;
    top.public_top->public_property_initializer_finish();
    if (s_finishCount != 3 || top.public_top->property_initializer_after != 0
        || top.public_top->property_constructor_after != 0
        || top.public_top->property_commit_after != 0
        || !top.public_top->public_property_object_is_null()) {
        std::fprintf(stderr,
                     "%%Error: property finish count=%u initializer=%u constructor=%u "
                     "commit=%u null=%u exp=3,0,0,0,1\n",
                     s_finishCount,
                     static_cast<unsigned>(top.public_top->property_initializer_after),
                     static_cast<unsigned>(top.public_top->property_constructor_after),
                     static_cast<unsigned>(top.public_top->property_commit_after),
                     static_cast<unsigned>(top.public_top->public_property_object_is_null()));
        return 1;
    }
    top.public_top->property_finish = false;
    top.public_top->public_property_initializer_finish();
    if (s_finishCount != 3 || top.public_top->property_initializer_after != 1
        || top.public_top->property_constructor_after != 1
        || top.public_top->property_commit_after != 1
        || top.public_top->public_property_object_is_null()) {
        std::fprintf(stderr,
                     "%%Error: property complete count=%u initializer=%u constructor=%u "
                     "commit=%u null=%u exp=3,1,1,1,0\n",
                     s_finishCount,
                     static_cast<unsigned>(top.public_top->property_initializer_after),
                     static_cast<unsigned>(top.public_top->property_constructor_after),
                     static_cast<unsigned>(top.public_top->property_commit_after),
                     static_cast<unsigned>(top.public_top->public_property_object_is_null()));
        return 1;
    }

    top.public_top->implicit_property_finish = true;
    top.public_top->public_implicit_property_initializer_finish();
    if (s_finishCount != 4 || top.public_top->implicit_property_initializer_after != 0
        || top.public_top->implicit_property_commit_after != 0
        || !top.public_top->public_implicit_property_object_is_null()) {
        std::fprintf(
            stderr,
            "%%Error: implicit property finish count=%u initializer=%u "
            "commit=%u null=%u exp=4,0,0,1\n",
            s_finishCount,
            static_cast<unsigned>(top.public_top->implicit_property_initializer_after),
            static_cast<unsigned>(top.public_top->implicit_property_commit_after),
            static_cast<unsigned>(top.public_top->public_implicit_property_object_is_null()));
        return 1;
    }
    top.public_top->implicit_property_finish = false;
    top.public_top->public_implicit_property_initializer_finish();
    if (s_finishCount != 4 || top.public_top->implicit_property_initializer_after != 1
        || top.public_top->implicit_property_commit_after != 1
        || top.public_top->public_implicit_property_object_is_null()) {
        std::fprintf(
            stderr,
            "%%Error: implicit property complete count=%u initializer=%u "
            "commit=%u null=%u exp=4,1,1,0\n",
            s_finishCount,
            static_cast<unsigned>(top.public_top->implicit_property_initializer_after),
            static_cast<unsigned>(top.public_top->implicit_property_commit_after),
            static_cast<unsigned>(top.public_top->public_implicit_property_object_is_null()));
        return 1;
    }

    top.eval();
    if (s_finishCount != 5) {
        std::fprintf(stderr, "%%Error: nested finish count=%u exp=5\n", s_finishCount);
        return 1;
    }
    if (top.public_top->nested_after != 0 || top.public_top->initial_after != 0) {
        std::fprintf(stderr, "%%Error: nested_after=%u initial_after=%u exp=0,0\n",
                     static_cast<unsigned>(top.public_top->nested_after),
                     static_cast<unsigned>(top.public_top->initial_after));
        return 1;
    }
    if (context.gotFinish()) {
        std::fprintf(stderr, "%%Error: custom finish callback latched gotFinish\n");
        return 1;
    }

    top.final();
    if (s_finishCount != 6 || top.public_top->final_after != 0) {
        std::fprintf(stderr, "%%Error: final finish count=%u after=%u exp=6,0\n", s_finishCount,
                     static_cast<unsigned>(top.public_top->final_after));
        return 1;
    }
    std::printf("*-* All Finished *-*\n");
    return 0;
}
