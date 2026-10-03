// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilated.h"

#include <cstdint>
#include <cstdlib>
#include <iostream>
#include VM_PREFIX_INCLUDE

namespace {

struct Expected final {
    uint8_t serial0 = 1;
    uint8_t serial1 = 2;
    uint8_t ringA = 4;
    uint8_t ringB = 5;
    uint8_t direct = 3;
    uint8_t fallback = 6;
    uint8_t parent = 9;
};

uint8_t trunc7(unsigned value) { return value & 0x7f; }

void checkValue(const char* name, unsigned got, unsigned expected) {
    if (got == expected) return;
    std::cerr << "%Error: " << name << " got=" << got << " expected=" << expected << '\n';
    std::exit(1);
}

void checkOutputs(VM_PREFIX* const top, const Expected& expected, uint8_t data) {
    checkValue("serial0", top->serial0, expected.serial0);
    checkValue("serial1", top->serial1, expected.serial1);
    checkValue("ring_a", top->ring_a, expected.ringA);
    checkValue("ring_b", top->ring_b, expected.ringB);
    checkValue("direct", top->direct, expected.direct);
    checkValue("fallback", top->fallback, expected.fallback);
    checkValue("parent_q", top->parent_q, expected.parent);
    checkValue("combo", top->combo, trunc7(expected.serial1 + expected.ringB) ^ data);
}

void evalWithoutEdge(VM_PREFIX* const top, const Expected& expected, uint8_t data) {
    top->data = data;
    top->eval();
    checkOutputs(top, expected, data);
    top->eval();
    checkOutputs(top, expected, data);
}

void evalPosedge(VM_PREFIX* const top, Expected& expected, uint8_t data, bool reset) {
    const Expected previous = expected;
    top->data = data;
    top->reset = reset;
    top->clk = 1;
    top->eval();

    if (reset) {
        expected = Expected{10, 11, 12, 13, 16, 15, 14};
    } else {
        expected.serial0 = trunc7(data + 3);
        expected.serial1 = previous.serial0 ^ 0x2a;
        expected.ringA = trunc7(previous.ringB + previous.serial0 + previous.parent);
        expected.ringB = previous.ringA ^ data;
        expected.direct = previous.serial0;
        expected.fallback = data;
        expected.parent = trunc7(previous.ringA + data);
    }
    checkOutputs(top, expected, data);

    top->clk = 0;
    top->eval();
    checkOutputs(top, expected, data);
}

}  // namespace

int main() {
    VM_PREFIX* const top = new VM_PREFIX{};
    Expected expected;

    top->clk = 0;
    top->reset = 0;
    top->data = 6;
    top->eval();
    checkOutputs(top, expected, 6);

    evalWithoutEdge(top, expected, 17);
    evalPosedge(top, expected, 23, true);
    evalWithoutEdge(top, expected, 41);
    evalPosedge(top, expected, 7, false);
    evalWithoutEdge(top, expected, 59);
    evalPosedge(top, expected, 31, false);
    evalPosedge(top, expected, 65, false);

    VL_DO_DANGLING(delete top, top);
    std::cout << "*-* All Finished *-*" << std::endl;
    return 0;
}
