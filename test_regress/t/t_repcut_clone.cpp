// DESCRIPTION: Verilator: Fixed-worker process clone regression
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"

#include <cstdio>
#include <cstring>
#include <unistd.h>

#include <sys/wait.h>

#include VM_PREFIX_INCLUDE

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

int errors = 0;

struct CheckedModel final {
    VM_PREFIX model;
    unsigned a = 0x13;
    unsigned b = 0x29;
    uint32_t random = 17;

    explicit CheckedModel(VerilatedContext* contextp, const char* name = "TOP")
        : model{contextp, name} {
        model.clk_a = 0;
        model.clk_b = 0;
        model.value = 0;
    }
    void check() {
        TEST_CHECK_EQ(model.a, a);
        TEST_CHECK_EQ(model.b, b);
        TEST_CHECK_EQ(model.combined, a ^ b);
    }
    void step() {
        random ^= random << 13;
        random ^= random >> 17;
        random ^= random << 5;
        model.value = random & 127;
        model.eval();
        model.clk_a = 1;
        model.eval();
        a = (a + model.value) & 127;
        check();
        model.clk_a = 0;
        model.clk_b = 1;
        model.eval();
        b ^= model.value;
        check();
        model.clk_b = 0;
        model.eval();
        check();
    }
};

// Return false in the child so main returns normally and runs model/context
// destructors. Both processes resume from the same independently checked state.
bool cloneCase(bool prepare, unsigned warmup, bool evaluateChild) {
    VerilatedContext context;
    context.threads(CLONE_THREADS);
    CheckedModel model{&context};
    for (unsigned i = 0; i < warmup; ++i) model.step();
    for (unsigned round = 0; round < 2; ++round) {
        if (prepare) model.model.prepareClone();
        const pid_t pid = fork();
        if (pid < 0) VL_FATAL_MT(__FILE__, __LINE__, "", "fork failed");
        alarm(30);
        if (pid == 0) {
            model.model.atClone();
            if (evaluateChild) {
                for (unsigned i = 0; i < 13 + round; ++i) model.step();
                // A new model retires while the cloned model still uses the same pool.
                CheckedModel other{&context, "other"};
                for (unsigned i = 0; i < 7; ++i) {
                    other.step();
                    model.step();
                }
            }
            return false;
        }
        if (prepare) model.model.atClone();
        for (unsigned i = 0; i < 11 + round; ++i) model.step();
        int status = 0;
        TEST_CHECK_EQ(waitpid(pid, &status, 0), pid);
        TEST_CHECK_EQ(WIFEXITED(status), true);
        if (WIFEXITED(status)) TEST_CHECK_EQ(WEXITSTATUS(status), 0);
    }
    return true;
}

void destroyPreparedModels() {
    VerilatedContext context;
    context.threads(CLONE_THREADS);
    CheckedModel first{&context, "first"};
    CheckedModel second{&context, "second"};
    for (unsigned i = 0; i < 7; ++i) {
        first.step();
        second.step();
    }
    first.model.prepareClone();
    // The shared pool has already been deleted. Clearing this second model
    // must not touch its former workers, nor may either destructor do so.
    second.model.prepareClone();
}

int main(int argc, char** argv) {
    setvbuf(stdout, nullptr, _IONBF, 0);
    alarm(30);
    // Omitting prepareClone deliberately leaks the child's inherited pool, as
    // in the stock API. Leak-checking runs can select only the prepared cases.
    const bool prepareOnly = argc > 1 && std::strcmp(argv[1], "prepare-only") == 0;
    for (const bool prepare : {true, false}) {
        if (prepareOnly && !prepare) continue;
        for (const unsigned warmup : {0U, 7U}) {
            for (const bool evaluateChild : {false, true}) {
                if (!cloneCase(prepare, warmup, evaluateChild)) return errors ? 1 : 0;
            }
        }
    }
    destroyPreparedModels();
    if (errors) return 1;
    VL_PRINTF("*-* All Finished *-*\n");
    return 0;
}
