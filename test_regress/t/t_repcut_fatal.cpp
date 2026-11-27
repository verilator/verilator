// DESCRIPTION: Verilator: Fixed-worker fatal shutdown regression
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"

#include <memory>

#include VM_PREFIX_INCLUDE

// std::exit runs this destructor after the fatal handler deletes the worker pool.
struct StaticModel final {
    VerilatedContext context;
    std::unique_ptr<VM_PREFIX> model;
    StaticModel() {
        context.threads(2);
        model.reset(new VM_PREFIX{&context});
    }
    ~StaticModel() {
        model.reset();
        VL_PRINTF("Static model destroyed\n");
    }
};

int main() {
    static StaticModel state;
    state.model->clk_a = 0;
    state.model->clk_b = 0;
    state.model->value = 3;
    state.model->eval();
    for (unsigned i = 0; i < 8; ++i) {
        state.model->clk_a = !state.model->clk_a;
        state.model->clk_b = !state.model->clk_b;
        state.model->eval();
    }
    VL_FATAL_MT("", 0, "", "Expected fatal shutdown");
}
