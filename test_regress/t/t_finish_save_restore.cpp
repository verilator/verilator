// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Save and restore $finish propagation state
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0
//
//*************************************************************************

#include "verilated.h"
#include "verilated_save.h"

#include "Vt_finish_save_restore.h"

#include <cinttypes>
#include <cstdio>
#include <cstring>

namespace {
unsigned s_finishCount = 0;
}

void vl_finish(const char*, int, const char*) VL_MT_UNSAFE { ++s_finishCount; }

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    Vt_finish_save_restore top{&context};

    top.trigger = 0;
    top.eval();
    top.trigger = 1;
    top.eval();
    if (s_finishCount != 1 || context.finishEpoch() != 1 || top.after != 0) {
        std::fprintf(stderr,
                     "%%Error: First finish count=%u epoch=%" PRIu64 " after=%u exp=1,1,0\n",
                     s_finishCount, context.finishEpoch(), static_cast<unsigned>(top.after));
        return 1;
    }

    const char* const saveArgp = context.commandArgsPlusMatch("SAVE_FILE=");
    if (!saveArgp[0]) {
        std::fprintf(stderr, "%%Error: Missing +SAVE_FILE argument\n");
        return 1;
    }
    const char* const saveFilenamep = saveArgp + std::strlen("+SAVE_FILE=");
    {
        VerilatedSave save;
        save.open(saveFilenamep);
        save << top;
        save.close();
    }

    top.trigger = 0;
    top.eval();
    top.trigger = 1;
    top.eval();
    if (s_finishCount != 2 || context.finishEpoch() != 2 || top.after != 0) {
        std::fprintf(stderr,
                     "%%Error: Second finish count=%u epoch=%" PRIu64 " after=%u exp=2,2,0\n",
                     s_finishCount, context.finishEpoch(), static_cast<unsigned>(top.after));
        return 1;
    }

    {
        VerilatedRestore restore;
        restore.open(saveFilenamep);
        restore >> top;
        restore.close();
    }
    if (context.finishEpoch() != 1) {
        std::fprintf(stderr, "%%Error: Restored finish epoch=%" PRIu64 " exp=1\n",
                     context.finishEpoch());
        return 1;
    }

    std::printf("*-* All Finished *-*\n");
    return 0;
}
