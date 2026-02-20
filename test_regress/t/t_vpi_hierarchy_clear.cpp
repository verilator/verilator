// ======================================================================
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Christian Hecken
// SPDX-License-Identifier: CC0-1.0
// ======================================================================

// DESCRIPTION: Scope hierarchy map clearing upon VerilatedModel destruction
//
// VerilatedImp::s() is a VerilatedImpData singleton that contains an m_hierMap
// whose keys are pointers to VerilatedScope objects. Because it is a
// singleton, it is not automatically destroyed together with the
// VerilatedModel, so this test checks that the VerilatedSyms destructor that is
// invoked upon the VerilatedModel's destruction clears the keys from the map.

// Workaround to be able to include verilated_imp.h, needed to directly test the hierarchy map
#define VERILATOR_VERILATED_CPP_
#include "verilated_imp.h"
#include <verilated.h>

#include "TestVpi.h"
#include "Vt_vpi_hierarchy_clear.h"
#include "Vt_vpi_hierarchy_clear__Syms.h"

#include <memory>

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    // Vt_vpi_hierarchy_clear::vlSymsp is private, so create a dummy syms object just to be able to
    // construct the VerilatedScope objects
    std::unique_ptr<Vt_vpi_hierarchy_clear__Syms> dummySymsp
        = std::make_unique<Vt_vpi_hierarchy_clear__Syms>(contextp.get(), "dummySymsObject",
                                                         nullptr);
    std::unique_ptr<VerilatedScope> additionalScope
        = std::make_unique<VerilatedScope>(dummySymsp.get(), "t.additional", "additional",
                                           "Additional", -12, VerilatedScope::SCOPE_MODULE);

    {
        // Construct and destroy
        const std::unique_ptr<VM_PREFIX> topp{
            new VM_PREFIX{contextp.get(),
                          // Note null name - we're flattening it out
                          ""}};

        // Insert additional scope into map for the first topp
        VerilatedImp::hierarchyAdd(additionalScope.get(), nullptr);
        const bool scopeFound = (VerilatedImp::hierarchyMap()->find(additionalScope.get())
                                 != VerilatedImp::hierarchyMap()->end());
        CHECK_RESULT_NZ(scopeFound);  // NOLINT(concurrency-mt-unsafe)
    }

    // Test second construction
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(),
                                                        // Note null name - we're flattening it out
                                                        ""}};

    // Do not insert additionalScope this time, so it should not be present in the map any more
    const bool scopeFound = (VerilatedImp::hierarchyMap()->find(additionalScope.get())
                             != VerilatedImp::hierarchyMap()->end());
    CHECK_RESULT_Z(scopeFound);  // NOLINT(concurrency-mt-unsafe)

    return 0;
}
