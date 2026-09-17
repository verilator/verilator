// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Hyeonuk Jeong
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilated_covergroup.h"

#include <atomic>
#include <thread>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

int errors = 0;

int main() {
    VerilatedContext context;
    std::atomic<bool> start{false};
    constexpr uint32_t iterations = 4093;
    auto create = [&]() {
        while (!start.load(std::memory_order_acquire)) std::this_thread::yield();
        // Exercise concurrent lazy registry creation as well as type lookup,
        // instance insertion, swap-on-retirement, and introspection.
        VlCovRegistry* const registryp = context.covergroupRegistryp();
        for (uint32_t i = 0; i < iterations; ++i) {
            VlCovInstHandle handle;
            const std::string name = "type" + std::to_string(i % 7);
            handle.attach(registryp->newCovergroupInst(name.c_str()));
            VlCoverpointT<1>* const cpp = handle.p()->addCoverpoint<1>();
            cpp->init("cp", 1, 2);
            cpp->addArrayNamer(VlCovBinKind::KIND_NORMAL, 2, "bins", __FILE__, __LINE__, 0);
            cpp->incrementBin(0);
            registryp->liveInstanceCount();
            registryp->createdInstanceCount(name.c_str());
            registryp->retiredInstanceCount(name.c_str());
            registryp->retiredCoverage(name.c_str());
        }
    };
    std::thread first{create};
    std::thread second{create};
    start.store(true, std::memory_order_release);
    first.join();
    second.join();
    VlCovRegistry* const registryp = context.covergroupRegistryp();
    TEST_CHECK_EQ(registryp->createdInstanceCount(), 2 * iterations);
    TEST_CHECK_EQ(registryp->liveInstanceCount(), 0);
    for (uint32_t i = 0; i < 7; ++i) {
        const std::string name = "type" + std::to_string(i);
        const uint32_t count = 2 * (iterations / 7 + (i < iterations % 7));
        TEST_CHECK_EQ(registryp->createdInstanceCount(name.c_str()), count);
        TEST_CHECK_EQ(registryp->retiredInstanceCount(name.c_str()), count);
        TEST_CHECK_EQ(registryp->retiredCoverage(name.c_str()), 50.0);
    }

    {
        VlCovInstHandle shared;
        shared.attach(registryp->newCovergroupInst("shared"));
        start.store(false, std::memory_order_relaxed);
        auto copy = [&]() {
            while (!start.load(std::memory_order_acquire)) std::this_thread::yield();
            for (uint32_t i = 0; i < iterations; ++i) {
                VlCovInstHandle handle{shared};
                VlCovInstHandle another{handle};
            }
        };
        std::thread third{copy};
        std::thread fourth{copy};
        start.store(true, std::memory_order_release);
        third.join();
        fourth.join();
        TEST_CHECK_EQ(registryp->liveInstanceCount("shared"), 1);
    }
    TEST_CHECK_EQ(registryp->liveInstanceCount(), 0);
    TEST_CHECK_EQ(registryp->createdInstanceCount("shared"), 1);
    TEST_CHECK_EQ(registryp->createdInstanceCount("unknown"), 0);
    TEST_CHECK_EQ(registryp->liveInstanceCount("unknown"), 0);
    TEST_CHECK_EQ(registryp->retiredInstanceCount("unknown"), 0);
    TEST_CHECK_EQ(registryp->retiredCoverage("unknown"), -1.0);
    if (errors) return 1;
    VL_PRINTF("*-* All Finished *-*\n");
    return 0;
}
