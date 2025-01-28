// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2013-2025 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "vpi_user.h"

#include <cstring>
#include <sstream>

class TestSimulator {
private:
    struct SimTypes {
        bool verilator = false;
        bool icarus = false;
        bool mti = false;
        bool ncsim = false;
        bool vcs = false;
        bool questa = false;
    };
    s_vpi_vlog_info m_info;
    SimTypes m_simulators;

public:
    TestSimulator() {
        vpi_get_vlog_info(&m_info);
        if (0 == std::strcmp(m_info.product, "Verilator")) {
            m_simulators.verilator = true;
        } else if (0 == std::strcmp(m_info.product, "Icarus Verilog")) {
            m_simulators.icarus = true;
        } else if (0
                   == strncmp(m_info.product, "Chronologic Simulation VCS",
                              std::strlen("Chronologic Simulation VCS"))) {
            m_simulators.vcs = true;
        } else if (0 == strcmp(m_info.product, "ModelSim for Questa-64")) {
            m_simulators.questa = true;
        } else {
            printf("%%Warning: %s:%d: Unknown simulator in TestSimulator.h: %s\n", __FILE__,
                   __LINE__, m_info.product);
        }
    }
    ~TestSimulator() = default;
    // METHORS
private:
    static TestSimulator& singleton() {
        static TestSimulator s_singleton;
        return s_singleton;
    }
    static const SimTypes& simulators() { return singleton().m_simulators; }

public:
    static const s_vpi_vlog_info& get_info() { return singleton().m_info; }
    // Simulator names
    static bool is_icarus() { return simulators().icarus; }
    static bool is_verilator() { return simulators().verilator; }
    static bool is_mti() { return simulators().mti; }
    static bool is_ncsim() { return simulators().ncsim; }
    static bool is_vcs() { return simulators().vcs; }
    static bool is_questa() { return simulators().questa; }
    // Simulator properties
    static bool is_event_driven() { return !simulators().verilator; }
    static bool has_get_scalar() { return !simulators().icarus; }
    // return test level scope
    static const char* top() {
        if (simulators().verilator || simulators().icarus || simulators().questa) {
            return "t";
        } else {
            return "top.t";
        }
    }
    // return absolute scope of obj
    static const char* rooted(const char* obj) {
        static std::string buf;
        std::ostringstream os;
        os << top();
        if (*obj) os << "." << obj;
        buf = os.str();
        return buf.c_str();
    }
};

#define VPI_HANDLE(signal) \
    vpi_handle_by_name(const_cast<PLI_BYTE8*>(TestSimulator::rooted(signal)), nullptr);
