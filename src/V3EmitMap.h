// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit a technology-mapped (LUT/FF/BRAM) netlist
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************
#ifndef VERILATOR_V3EMITMAP_H_
#define VERILATOR_V3EMITMAP_H_
#include "config_build.h"
#include "verilatedos.h"
#include <string>
class V3EmitMap final {
public:
    // Map the whole design with libabc and write yosys-JSON for nextpnr
    static void emit(const std::string& filename) VL_MT_DISABLED;
};
#endif  // Guard
