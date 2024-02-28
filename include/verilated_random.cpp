// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2024 by Antmicro Ltd.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU Lesser
// General Public License Version 3 or the Perl Artistic License Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=========================================================================
///
/// \file
/// \brief Verilated randomization implementation code
///
/// This file must be compiled and linked against all Verilated objects
/// that use randomization features.
///
/// See the internals documentation docs/internals.rst for details.
///
//=========================================================================

#include "verilated_random.h"

#include <fstream>
#include <sstream>

#include <sys/wait.h>

#define HASH_LEN 1

static const char* solvers[] = {
    "z3 ",
    "cvc5 --lang=smt2 ",
    "cvc4 --lang=smt2 ",
};

static std::string get_solver() {
    static std::string solver;
    static bool found = false;
    if (found) return solver;

    for (const char* cmd : solvers) {
        std::string comm = cmd + std::string{"/dev/null 2>/dev/null"};
        int ec = system(comm.c_str());
        if (!ec) {
            solver = cmd;
            found = true;
            return solver;
        }
    }
    std::stringstream msg;
    msg << "No SAT solvers found, please install one of them.  Tried:\n";
    for (const char* cmd : solvers) msg << "$ " << cmd << '\n';

    VL_WARN_MT("", 0, "randomize", msg.str().c_str());

    found = true;
    return solver;
}

//======================================================================
// VlRandomizer:: Methods

void VlRandomVar::emit(std::ostream& s) const { s << m_name; }

bool VlRandomizer::next() {
    std::string cmd = get_solver();
    if (cmd == "") return false;

    char filename[] = "/tmp/VrandomXXXXXX";
    int fd = mkstemp(filename);
    if (fd == -1) return false;
    close(fd);
    std::ofstream f{filename};
    f << "(set-option :produce-models true)\n";
    f << "(set-logic QF_BV)\n\n";
    for (const auto& var : m_vars) {
        f << "(declare-fun " << var.second->name() << " () (_ BitVec " << var.second->width()
          << "))\n";
    }
    for (const auto& constraint : m_constraints) { f << "(assert " << constraint << ")\n"; }
    f << "\n(check-sat)\n";
    f << "(get-value (";
    for (const auto& var : m_vars) { f << var.second->name() << ' '; }
    f << "))\n";
    f << "(exit)\n";
    f.close();

    int rc = 3;
    std::string comm = cmd + filename;
    FILE* solver = popen(comm.c_str(), "r");
    if (solver) {
        rc = parse_solution(solver);
        int ec = pclose(solver);
        if (rc == 2) {
            std::stringstream msg;
            msg << "Error processing output of `" << comm << "' command";
            VL_WARN_MT("", 0, "randomize", msg.str().c_str());
        }
        if (WIFSIGNALED(ec) || WEXITSTATUS(ec) > (rc == 2 ? 0 : 1)) {
            std::stringstream msg;
            msg << "Command `" << comm
                << "' failed: " << (WIFSIGNALED(ec) ? "terminated by signal" : "exit status")
                << ' ' << (WIFSIGNALED(ec) ? WTERMSIG(ec) : WEXITSTATUS(ec))
                << (WIFSIGNALED(ec) && WCOREDUMP(ec) ? " (core dumped)" : "");
            VL_WARN_MT("", 0, "randomize", msg.str().c_str());
        }
    }

    unlink(filename);
    return rc == 0;
}

int VlRandomizer::parse_solution(FILE* solver) {
    ssize_t n = getline(&m_line, &m_capacity, solver);
    if (n < 0) return 3;
    std::string sat{m_line, (size_t)n};
    if (sat == "unsat\n") return 1;
    if (sat != "sat\n") { VL_WARN_MT("", 0, "randomize", sat.c_str()); }

    // Quasi-parse S-expression of the form ((x #xVALUE) (y #bVALUE) (z #xVALUE))
    n = getdelim(&m_line, &m_capacity, '(', solver);
    if (n <= 0) return 2;

    for (;;) {
        n = getdelim(&m_line, &m_capacity, '(', solver);
        if (n < 0) return 2;
        if (n == 0 || m_line[n - 1] != '(') break;
        n = getdelim(&m_line, &m_capacity, ' ', solver);
        if (n <= 1) return 2;

        std::string name{m_line, (size_t)n - 1};

        n = getdelim(&m_line, &m_capacity, ')', solver);
        if (n <= 0) return 2;

        const char* value = m_line;

        auto it = m_vars.find(name);
        if (it == m_vars.end()) continue;

        int base = 0;
        if (value[0] == '#') {
            value++;
            base = value[0] == 'x' ? 16 : value[0] == 'b' ? 2 : value[0] == 'o' ? 8 : 10;
            if (base != 10) value++;
        }
        unsigned long long val = strtoull(value, nullptr, base);
        it->second->set(val);
    }

    return 0;
}
VlRandomizer::~VlRandomizer() { std::free(m_line); }

void VlRandomizer::hard(std::string&& constraint) {
    m_constraints.emplace_back(std::move(constraint));
}

#ifdef VL_DEBUG
void VlRandomizer::dump() const { VL_PRINTF("Randomizer seed %d\n", 55); }
#endif
