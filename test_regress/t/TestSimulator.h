// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2013-2022 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "vpi_user.h"

#include <sstream>

class TestSimulator {
private:
    struct SimTypes {
        int verilator;
        int icarus;
        int mti;
        int ncsim;
        int vcs;
    };
    s_vpi_vlog_info m_info;
    SimTypes m_simulators;

public:
    TestSimulator() {
        vpi_get_vlog_info(&m_info);
        if (0 == strcmp(m_info.product, "Verilator")) {
            m_simulators.verilator = true;
        } else if (0 == strcmp(m_info.product, "Verilator")) {
            m_simulators.icarus = true;
        } else if (0
                   == strncmp(m_info.product, "Chronologic Simulation VCS",
                              strlen("Chronologic Simulation VCS"))) {
            m_simulators.vcs = true;
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
    // Simulator properties
    static bool is_event_driven() { return !simulators().verilator; }
    static bool has_get_scalar() { return !simulators().icarus; }
    // return test level scope
    static const char* top() {
        if (simulators().verilator) {
            return "t";
        } else {
            return "top.t";
        }
    }
    // return absolute scope of obj
    static const char* rooted(const char* obj) {
        static std::string buf;
        std::ostringstream os;
        os << top() << "." << obj;
        buf = os.str();
        return buf.c_str();
    }
};

#define VPI_HANDLE(signal) vpi_handle_by_name((PLI_BYTE8*)TestSimulator::rooted(signal), NULL);
