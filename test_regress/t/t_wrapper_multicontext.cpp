// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include <iostream>
#include <memory>
#include <svdpi.h>
#include <vector>

#include VM_PREFIX_INCLUDE

static int test_key;

extern "C" void test_dpi();

class Tester {
private:
    std::unique_ptr<VerilatedContext> ctx;
    std::unique_ptr<VM_PREFIX> dut;

public:
    Tester() {
        ctx = std::make_unique<VerilatedContext>();
        dut = std::make_unique<VM_PREFIX>(ctx.get());
    }

    void run_test() {
        dut->clk = 0;
        dut->eval();
        dut->clk = 1;
        dut->eval();
    }

    void put(const char* strp) {
        Verilated::threadContextp(ctx.get());
        const svScope scope = svGetScopeFromName("TOP.test");
        svPutUserData(scope, &test_key, (void*)strp);
    }
};

const char* messages[] = {"This ", "is ", "a ", "test ", "message.\n"};

int main() {
    std::vector<Tester> testers;
    for (auto message : messages) {
        testers.emplace_back();
        testers.back().put(message);
    }
    for (auto& t : testers) t.run_test();
    return 0;
}

extern "C" void test_dpi() {
    const svScope scope = svGetScope();
    void* const strp = svGetUserData(scope, &test_key);
    std::cout << static_cast<const char*>(strp);
}
