// DESCRIPTION: Verilator: Verilog Test main for functional coverage
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#include "verilated.h"
#include "verilated_funccov.h"
#include VM_PREFIX_INCLUDE

#include <iostream>
#include <memory>

// Test the functional coverage runtime infrastructure
void testFuncCovInfrastructure() {
    std::cout << "Testing functional coverage infrastructure..." << std::endl;

    // Create a covergroup
    VerilatedCovergroup cg("test_cg");

    // Create a coverpoint with automatic bins
    auto* cp_addr = new VerilatedCoverpoint{"cp_addr"};
    cp_addr->addBin(new VerilatedCoverRangeBin{"low", 0, 127});
    cp_addr->addBin(new VerilatedCoverRangeBin{"high", 128, 255});
    cg.addCoverpoint(cp_addr);

    // Create another coverpoint
    auto* cp_cmd = new VerilatedCoverpoint{"cp_cmd"};
    cp_cmd->addBin(new VerilatedCoverRangeBin{"read", 0, 0});
    cp_cmd->addBin(new VerilatedCoverRangeBin{"write", 1, 1});
    cg.addCoverpoint(cp_cmd);

    // Create a cross coverage
    auto* cross = new VerilatedCoverCross{"cross_cmd_addr"};
    cross->addCoverpoint(cp_addr);
    cross->addCoverpoint(cp_cmd);
    cg.addCross(cross);

    // Sample some values
    std::cout << "Sampling values..." << std::endl;
    cp_addr->sample(10);  // low bin
    cp_cmd->sample(0);  // read bin
    cross->sample({10, 0});

    cp_addr->sample(200);  // high bin
    cp_cmd->sample(1);  // write bin
    cross->sample({200, 1});

    cp_addr->sample(50);  // low bin again
    cp_cmd->sample(0);  // read bin again
    cross->sample({50, 0});

    // Check coverage
    double addr_cov = cp_addr->getCoverage();
    double cmd_cov = cp_cmd->getCoverage();
    double cross_cov = cross->getCoverage();
    double cg_cov = cg.get_coverage();

    std::cout << "cp_addr coverage: " << addr_cov << "%" << std::endl;
    std::cout << "cp_cmd coverage: " << cmd_cov << "%" << std::endl;
    std::cout << "cross coverage: " << cross_cov << "%" << std::endl;
    std::cout << "Covergroup coverage: " << cg_cov << "%" << std::endl;

    // Verify results
    if (addr_cov != 100.0) {
        std::cerr << "ERROR: Expected addr coverage 100%, got " << addr_cov << std::endl;
        exit(1);
    }
    if (cmd_cov != 100.0) {
        std::cerr << "ERROR: Expected cmd coverage 100%, got " << cmd_cov << std::endl;
        exit(1);
    }
    // Cross coverage should be 50% (2 out of 4 possible cross products covered)
    if (cross_cov < 49.9 || cross_cov > 50.1) {
        std::cerr << "ERROR: Expected cross coverage ~50%, got " << cross_cov << std::endl;
        exit(1);
    }
    // Overall covergroup coverage is weighted average of all components
    // (100 + 100 + 50) / 3 = 83.33%
    if (cg_cov < 83.0 || cg_cov > 84.0) {
        std::cerr << "ERROR: Expected covergroup coverage ~83.33%, got " << cg_cov << std::endl;
        exit(1);
    }

    std::cout << "Functional coverage infrastructure test PASSED" << std::endl;
}

int main(int argc, char** argv) {
    // Standard Verilator setup
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get()}};

    // Test functional coverage infrastructure
    testFuncCovInfrastructure();

    // Run the Verilog simulation briefly
    contextp->timeInc(1);
    topp->eval();

    // Check for finish
    if (!contextp->gotFinish()) {
        VL_PRINTF("%%Error: main.cpp didn't finish\n");
        exit(1);
    }

    std::cout << "*-* All Finished *-*" << std::endl;
    return 0;
}
