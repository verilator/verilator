// -*- mode: C++; c-file-style: "cc-mode" -*-
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE

VM_PREFIX* tb = nullptr;

int main() {
    Verilated::debug(0);
    tb = new VM_PREFIX{"tb"};

    VL_PRINTF("*-* All Finished *-*\n");
    tb->final();
    VL_DO_DANGLING(delete tb, tb);
    return 0;
}

int sc_main(int argc, char* argv[]) {
    tb = new VM_PREFIX{"tb"};

    VL_PRINTF("*-* All Finished *-*\n");
    tb->final();
    VL_DO_DANGLING(delete tb, tb);
    return 0;
}
