// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2024 by Wilson Snyder.  This program is free software; you can
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

#include <iostream>
#include <sstream>
#include <streambuf>

#define _VL_SOLVER_HASH_LEN 1
#define _VL_SOLVER_HASH_LEN_TOTAL 4

// clang-format off
#if defined(__unix__) || defined(__unix) || (defined(__APPLE__) && defined(__MACH__))
# define _VL_SOLVER_PIPE  // Allow pipe SMT solving.  Needs fork()
#endif

#ifdef _VL_SOLVER_PIPE
# include <sys/wait.h>
# include <fcntl.h>
#endif

#if defined(_WIN32) || defined(__MINGW32__)
# include <io.h>  // open, read, write, close
#endif
// clang-format on

class Process final : private std::streambuf, public std::iostream {
    static constexpr int BUFFER_SIZE = 4096;
    const char* const* m_cmd = nullptr;  // fork() process argv
#ifdef _VL_SOLVER_PIPE
    pid_t m_pid = 0;  // fork() process id
#else
    int m_pid = 0;  // fork() process id - always zero as disabled
#endif
    bool m_pidExited = true;  // If subprocess has exited and can be opened
    int m_pidStatus = 0;  // fork() process exit status, valid if m_pidExited
    int m_writeFd = -1;  // File descriptor TO subprocess
    int m_readFd = -1;  // File descriptor FROM subprocess
    char m_readBuf[BUFFER_SIZE];
    char m_writeBuf[BUFFER_SIZE];

public:
    typedef std::streambuf::traits_type traits_type;

protected:
    int overflow(int c = traits_type::eof()) override {
        char c2 = static_cast<char>(c);
        if (pbase() == pptr()) return 0;
        size_t size = pptr() - pbase();
        ssize_t n = ::write(m_writeFd, pbase(), size);
        if (n == -1) perror("write");
        if (n <= 0) {
            wait_report();
            return traits_type::eof();
        }
        if (n == size)
            setp(m_writeBuf, m_writeBuf + sizeof(m_writeBuf));
        else
            setp(m_writeBuf + n, m_writeBuf + sizeof(m_writeBuf));
        if (c != traits_type::eof()) sputc(c2);
        return 0;
    }
    int underflow() override {
        sync();
        ssize_t n = ::read(m_readFd, m_readBuf, sizeof(m_readBuf));
        if (n == -1) perror("read");
        if (n <= 0) {
            wait_report();
            return traits_type::eof();
        }
        setg(m_readBuf, m_readBuf, m_readBuf + n);
        return traits_type::to_int_type(m_readBuf[0]);
    }
    int sync() override {
        overflow();
        return 0;
    }

public:
    explicit Process(const char* const* const cmd = nullptr)
        : std::streambuf{}
        , std::iostream{this}
        , m_cmd{cmd} {
        open(cmd);
    }

    void wait_report() {
        if (m_pidExited) return;
#ifdef _VL_SOLVER_PIPE
        if (waitpid(m_pid, &m_pidStatus, 0) != m_pid) return;
        if (m_pidStatus) {
            std::stringstream msg;
            msg << "Subprocess command `" << m_cmd[0];
            for (const char* const* arg = m_cmd + 1; *arg; arg++) msg << ' ' << *arg;
            msg << "' failed: ";
            if (WIFSIGNALED(m_pidStatus))
                msg << strsignal(WTERMSIG(m_pidStatus))
                    << (WCOREDUMP(m_pidStatus) ? " (core dumped)" : "");
            else if (WIFEXITED(m_pidStatus))
                msg << "exit status " << WEXITSTATUS(m_pidStatus);
            const std::string str = msg.str();
            VL_WARN_MT("", 0, "Process", str.c_str());
        }
#endif
        m_pidExited = true;
        m_pid = 0;
        closeFds();
    }

    void closeFds() {
        if (m_writeFd != -1) {
            close(m_writeFd);
            m_writeFd = -1;
        }
        if (m_readFd != -1) {
            close(m_readFd);
            m_readFd = -1;
        }
    }

    bool open(const char* const* const cmd) {
        setp(std::begin(m_writeBuf), std::end(m_writeBuf));
        setg(m_readBuf, m_readBuf, m_readBuf);
#ifdef _VL_SOLVER_PIPE
        if (!cmd || !cmd[0]) return false;
        m_cmd = cmd;
        int fd_stdin[2];  // Can't use std::array
        int fd_stdout[2];  // Can't use std::array
        constexpr int P_RD = 0;
        constexpr int P_WR = 1;

        if (pipe(fd_stdin) != 0) {
            perror("Process::open: pipe");
            return false;
        }
        if (pipe(fd_stdout) != 0) {
            perror("Process::open: pipe");
            close(fd_stdin[P_RD]);
            close(fd_stdin[P_WR]);
            return false;
        }

        if (fd_stdin[P_RD] <= 2 || fd_stdin[P_WR] <= 2 || fd_stdout[P_RD] <= 2
            || fd_stdout[P_WR] <= 2) {
            // We'd have to rearrange all of the FD usages in this case.
            // Too unlikely; verilator isn't a daemon.
            fprintf(stderr, "stdin/stdout closed before pipe opened\n");
            close(fd_stdin[P_RD]);
            close(fd_stdin[P_WR]);
            close(fd_stdout[P_RD]);
            close(fd_stdout[P_WR]);
            return false;
        }

        const pid_t pid = fork();
        if (pid < 0) {
            perror("Process::open: fork");
            close(fd_stdin[P_RD]);
            close(fd_stdin[P_WR]);
            close(fd_stdout[P_RD]);
            close(fd_stdout[P_WR]);
            return false;
        }
        if (pid == 0) {
            // Child
            close(fd_stdin[P_WR]);
            dup2(fd_stdin[P_RD], STDIN_FILENO);
            close(fd_stdout[P_RD]);
            dup2(fd_stdout[P_WR], STDOUT_FILENO);
            execvp(cmd[0], const_cast<char* const*>(cmd));
            std::stringstream msg;
            msg << "Process::open: execvp(" << cmd[0] << ")";
            const std::string str = msg.str();
            perror(str.c_str());
            _exit(127);
        }
        // Parent
        m_pid = pid;
        m_pidExited = false;
        m_pidStatus = 0;
        m_readFd = fd_stdout[P_RD];
        m_writeFd = fd_stdin[P_WR];

        close(fd_stdin[P_RD]);
        close(fd_stdout[P_WR]);

        return true;
#else
        return false;
#endif
    }
};

static Process& getSolver() {
    static Process s_solver;
    static bool s_done = false;
    if (s_done) return s_solver;
    s_done = true;

    static std::vector<const char*> s_argv;
    static std::string s_program = Verilated::threadContextp()->solverProgram();
    s_argv.emplace_back(&s_program[0]);
    for (char* arg = &s_program[0]; *arg; arg++) {
        if (*arg == ' ') {
            *arg = '\0';
            s_argv.emplace_back(arg + 1);
        }
    }
    s_argv.emplace_back(nullptr);

    const char* const* const cmd = &s_argv[0];
    s_solver.open(cmd);
    s_solver << "(set-logic QF_BV)\n";
    s_solver << "(check-sat)\n";
    s_solver << "(reset)\n";
    std::string s;
    getline(s_solver, s);
    if (s == "sat") return s_solver;

    std::stringstream msg;
    msg << "Unable to communicate with SAT solver, please check its installation or specify a "
           "different one in VERILATOR_SOLVER environment variable.\n";
    msg << " ... Tried: $";
    for (const char* const* arg = cmd; *arg; arg++) msg << ' ' << *arg;
    msg << '\n';
    const std::string str = msg.str();
    VL_WARN_MT("", 0, "randomize", str.c_str());

    while (getline(s_solver, s)) {}
    return s_solver;
}

//======================================================================
// VlRandomizer:: Methods

void VlRandomVar::emit(std::ostream& s) const { s << m_name; }
void VlRandomConst::emit(std::ostream& s) const {
    s << "#b";
    for (int i = 0; i < m_width; i++) s << (VL_BITISSET_Q(m_val, m_width - i - 1) ? '1' : '0');
}
void VlRandomBinOp::emit(std::ostream& s) const {
    s << '(' << m_op << ' ';
    m_lhs->emit(s);
    s << ' ';
    m_rhs->emit(s);
    s << ')';
}
void VlRandomExtract::emit(std::ostream& s) const {
    s << "((_ extract " << m_idx << ' ' << m_idx << ") ";
    m_expr->emit(s);
    s << ')';
}
bool VlRandomVar::set(std::string&& val) const {
    VlWide<VL_WQ_WORDS_E> qowp;
    VL_SET_WQ(qowp, 0ULL);
    WDataOutP owp = qowp;
    int obits = width();
    if (obits > VL_QUADSIZE) owp = reinterpret_cast<WDataOutP>(datap());
    int i;
    for (i = 0; val[i] && val[i] != '#'; i++) {}
    if (val[i++] != '#') return false;
    switch (val[i++]) {
    case 'b': _vl_vsss_based(owp, obits, 1, &val[i], 0, val.size() - i); break;
    case 'o': _vl_vsss_based(owp, obits, 3, &val[i], 0, val.size() - i); break;
    case 'h':  // FALLTHRU
    case 'x': _vl_vsss_based(owp, obits, 4, &val[i], 0, val.size() - i); break;
    default:
        VL_WARN_MT(__FILE__, __LINE__, "randomize",
                   "Internal: Unable to parse solver's randomized number");
        return false;
    }
    if (obits <= VL_BYTESIZE) {
        CData* const p = static_cast<CData*>(datap());
        *p = VL_CLEAN_II(obits, obits, owp[0]);
    } else if (obits <= VL_SHORTSIZE) {
        SData* const p = static_cast<SData*>(datap());
        *p = VL_CLEAN_II(obits, obits, owp[0]);
    } else if (obits <= VL_IDATASIZE) {
        IData* const p = static_cast<IData*>(datap());
        *p = VL_CLEAN_II(obits, obits, owp[0]);
    } else if (obits <= VL_QUADSIZE) {
        QData* const p = static_cast<QData*>(datap());
        *p = VL_CLEAN_QQ(obits, obits, VL_SET_QW(owp));
    } else {
        _vl_clean_inplace_w(obits, owp);
    }
    return true;
}

std::shared_ptr<const VlRandomExpr> VlRandomizer::randomConstraint(VlRNG& rngr, int bits) {
    unsigned long long hash = VL_RANDOM_RNG_I(rngr) & ((1 << bits) - 1);
    std::shared_ptr<const VlRandomExpr> concat = nullptr;
    std::vector<std::shared_ptr<const VlRandomExpr>> varbits;
    for (const auto& var : m_vars) {
        for (int i = 0; i < var.second->width(); i++)
            varbits.emplace_back(std::make_shared<const VlRandomExtract>(var.second, i));
    }
    for (int i = 0; i < bits; i++) {
        std::shared_ptr<const VlRandomExpr> bit = nullptr;
        for (unsigned j = 0; j * 2 < varbits.size(); j++) {
            unsigned idx = j + VL_RANDOM_RNG_I(rngr) % (varbits.size() - j);
            auto sel = varbits[idx];
            std::swap(varbits[idx], varbits[j]);
            bit = bit == nullptr ? sel : std::make_shared<const VlRandomBinOp>("bvxor", bit, sel);
        }
        concat = concat == nullptr ? bit
                                   : std::make_shared<const VlRandomBinOp>("concat", concat, bit);
    }
    return std::make_shared<const VlRandomBinOp>(
        "=", concat, std::make_shared<const VlRandomConst>(hash, bits));
}

bool VlRandomizer::next(VlRNG& rngr) {
    if (m_vars.empty()) return true;
    std::iostream& f = getSolver();
    if (!f) return false;

    f << "(set-option :produce-models true)\n";
    f << "(set-logic QF_BV)\n";
    for (const auto& var : m_vars) {
        f << "(declare-fun " << var.second->name() << " () (_ BitVec " << var.second->width()
          << "))\n";
    }
    for (const std::string& constraint : m_constraints) { f << "(assert " << constraint << ")\n"; }
    f << "(check-sat)\n";

    bool sat = parseSolution(f);
    if (!sat) {
        f << "(reset)\n";
        return false;
    }

    for (int i = 0; i < _VL_SOLVER_HASH_LEN_TOTAL && sat; i++) {
        f << "(assert ";
        randomConstraint(rngr, _VL_SOLVER_HASH_LEN)->emit(f);
        f << ")\n";
        f << "\n(check-sat)\n";
        sat = parseSolution(f);
    }

    f << "(reset)\n";
    return true;
}

bool VlRandomizer::parseSolution(std::iostream& f) {
    std::string sat;
    do { std::getline(f, sat); } while (sat == "");

    if (sat == "unsat") return false;
    if (sat != "sat") {
        std::stringstream msg;
        msg << "Internal: Solver error: " << sat;
        const std::string str = msg.str();
        VL_WARN_MT(__FILE__, __LINE__, "randomize", str.c_str());
        return false;
    }

    f << "(get-value (";
    for (const auto& var : m_vars) f << var.second->name() << ' ';
    f << "))\n";

    // Quasi-parse S-expression of the form ((x #xVALUE) (y #bVALUE) (z #xVALUE))
    char c;
    f >> c;
    if (c != '(') {
        VL_WARN_MT(__FILE__, __LINE__, "randomize",
                   "Internal: Unable to parse solver's response: invalid S-expression");
        return false;
    }

    while (true) {
        f >> c;
        if (c == ')') break;
        if (c != '(') {
            VL_WARN_MT(__FILE__, __LINE__, "randomize",
                       "Internal: Unable to parse solver's response: invalid S-expression");
            return false;
        }

        std::string name, value;
        f >> name;
        std::getline(f, value, ')');

        auto it = m_vars.find(name);
        if (it == m_vars.end()) continue;

        it->second->set(std::move(value));
    }

    return true;
}

void VlRandomizer::hard(std::string&& constraint) {
    m_constraints.emplace_back(std::move(constraint));
}

#ifdef VL_DEBUG
void VlRandomizer::dump() const {
    for (const auto& var : m_vars) {
        VL_PRINTF("Variable (%d): %s\n", var.second->width(), var.second->name());
    }
    for (const std::string& c : m_constraints) VL_PRINTF("Constraint: %s\n", c.c_str());
}
#endif
