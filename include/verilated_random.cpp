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
    s_solver << "(set-logic QF_ABV)\n";
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

std::string readUntilBalanced(std::istream& stream) {
    std::string result;
    std::string token;
    int parenCount = 1;
    while (stream >> token) {
        for (const char c : token) {
            if (c == '(') {
                ++parenCount;
            } else if (c == ')') {
                --parenCount;
            }
        }
        result += token + " ";
        if (parenCount == 0) break;
    }
    return result;
}

std::string parseNestedSelect(const std::string& nested_select_expr,
                              std::vector<std::string>& indices) {
    std::istringstream nestedStream(nested_select_expr);
    std::string name, idx;
    nestedStream >> name;
    if (name == "(select") {
        const std::string further_nested_expr = readUntilBalanced(nestedStream);
        name = parseNestedSelect(further_nested_expr, indices);
    }
    std::getline(nestedStream, idx, ')');
    indices.push_back(idx);
    return name;
}

std::string flattenIndices(const std::vector<std::string>& indices, const VlRandomVar* const var) {
    int flattenedIndex = 0;
    int multiplier = 1;
    for (int i = indices.size() - 1; i >= 0; --i) {
        int indexValue = 0;
        std::string trimmedIndex = indices[i];

        trimmedIndex.erase(0, trimmedIndex.find_first_not_of(" \t"));
        trimmedIndex.erase(trimmedIndex.find_last_not_of(" \t") + 1);

        if (trimmedIndex.find("#x") == 0) {
            indexValue = std::strtoul(trimmedIndex.substr(2).c_str(), nullptr, 16);
        } else if (trimmedIndex.find("#b") == 0) {
            indexValue = std::strtoul(trimmedIndex.substr(2).c_str(), nullptr, 2);
        } else {
            indexValue = std::strtoul(trimmedIndex.c_str(), nullptr, 10);
        }
        const int length = var->getLength(i);
        if (length == -1) {
            VL_WARN_MT(__FILE__, __LINE__, "randomize",
                       "Internal: Wrong Call: Only RandomArray can call getLength()");
            break;
        }
        flattenedIndex += indexValue * multiplier;
        multiplier *= length;
    }
    std::string hexString = std::to_string(flattenedIndex);
    while (hexString.size() < 8) { hexString.insert(0, "0"); }
    return "#x" + hexString;
}
//======================================================================
// VlRandomizer:: Methods

void VlRandomVar::emitGetValue(std::ostream& s) const { s << ' ' << m_name; }
void VlRandomVar::emitExtract(std::ostream& s, int i) const {
    s << " ((_ extract " << i << ' ' << i << ") " << m_name << ')';
}
void VlRandomVar::emitType(std::ostream& s) const { s << "(_ BitVec " << width() << ')'; }
int VlRandomVar::totalWidth() const { return m_width; }
static bool parseSMTNum(int obits, WDataOutP owp, const std::string& val) {
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
    return true;
}
bool VlRandomVar::set(const std::string& idx, const std::string& val) const {
    VlWide<VL_WQ_WORDS_E> qowp;
    VL_SET_WQ(qowp, 0ULL);
    WDataOutP owp = qowp;
    const int obits = width();
    VlWide<VL_WQ_WORDS_E> qiwp;
    VL_SET_WQ(qiwp, 0ULL);
    if (!idx.empty() && !parseSMTNum(64, qiwp, idx)) return false;
    const int nidx = qiwp[0];
    if (obits > VL_QUADSIZE) owp = reinterpret_cast<WDataOutP>(datap(nidx));
    if (!parseSMTNum(obits, owp, val)) return false;

    if (obits <= VL_BYTESIZE) {
        CData* const p = static_cast<CData*>(datap(nidx));
        *p = VL_CLEAN_II(obits, obits, owp[0]);
    } else if (obits <= VL_SHORTSIZE) {
        SData* const p = static_cast<SData*>(datap(nidx));
        *p = VL_CLEAN_II(obits, obits, owp[0]);
    } else if (obits <= VL_IDATASIZE) {
        IData* const p = static_cast<IData*>(datap(nidx));
        *p = VL_CLEAN_II(obits, obits, owp[0]);
    } else if (obits <= VL_QUADSIZE) {
        QData* const p = static_cast<QData*>(datap(nidx));
        *p = VL_CLEAN_QQ(obits, obits, VL_SET_QW(owp));
    } else {
        _vl_clean_inplace_w(obits, owp);
    }
    return true;
}

void VlRandomizer::randomConstraint(std::ostream& os, VlRNG& rngr, int bits) {
    const IData hash = VL_RANDOM_RNG_I(rngr) & ((1 << bits) - 1);
    int varBits = 0;
    for (const auto& var : m_vars) varBits += var.second->totalWidth();
    os << "(= #b";
    for (int i = bits - 1; i >= 0; i--) os << (VL_BITISSET_I(hash, i) ? '1' : '0');
    if (bits > 1) os << " (concat";
    for (int i = 0; i < bits; i++) {
        IData varBitsLeft = varBits;
        IData varBitsWant = (varBits + 1) / 2;
        if (varBits > 2) os << " (bvxor";
        for (const auto& var : m_vars) {
            for (int j = 0; j < var.second->totalWidth(); j++, varBitsLeft--) {
                const bool doEmit = (VL_RANDOM_RNG_I(rngr) % varBitsLeft) < varBitsWant;
                if (doEmit) {
                    var.second->emitExtract(os, j);
                    if (--varBitsWant == 0) break;
                }
            }
            if (varBitsWant == 0) break;
        }
        if (varBits > 2) os << ')';
    }
    if (bits > 1) os << ')';
    os << ')';
}

bool VlRandomizer::next(VlRNG& rngr) {
    if (m_vars.empty()) return true;
    std::iostream& f = getSolver();
    if (!f) return false;

    f << "(set-option :produce-models true)\n";
    f << "(set-logic QF_ABV)\n";
    f << "(define-fun __Vbv ((b Bool)) (_ BitVec 1) (ite b #b1 #b0))\n";
    f << "(define-fun __Vbool ((v (_ BitVec 1))) Bool (= #b1 v))\n";
    for (const auto& var : m_vars) {
        f << "(declare-fun " << var.second->name() << " () ";
        var.second->emitType(f);
        f << ")\n";
    }
    for (const std::string& constraint : m_constraints) {
        f << "(assert (= #b1 " << constraint << "))\n";
    }
    f << "(check-sat)\n";

    bool sat = parseSolution(f);
    if (!sat) {
        f << "(reset)\n";
        return false;
    }
    for (int i = 0; i < _VL_SOLVER_HASH_LEN_TOTAL && sat; i++) {
        f << "(assert ";
        randomConstraint(f, rngr, _VL_SOLVER_HASH_LEN);
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
    for (const auto& var : m_vars) var.second->emitGetValue(f);
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
        std::string name, idx, value;
        std::vector<std::string> indices;
        f >> name;
        indices.clear();
        if (name == "(select") {
            const std::string selectExpr = readUntilBalanced(f);
            name = parseNestedSelect(selectExpr, indices);
            idx = indices[0];
        }
        std::getline(f, value, ')');
        const auto it = m_vars.find(name);
        if (it == m_vars.end()) continue;
        const VlRandomVar& varr = *it->second;
        if (m_randmode && !varr.randModeIdxNone()) {
            if (!(m_randmode->at(varr.randModeIdx()))) continue;
        }
        if (indices.size() > 1) {
            const std::string flattenedIndex = flattenIndices(indices, &varr);
            varr.set(flattenedIndex, value);
        } else {
            varr.set(idx, value);
        }
    }
    return true;
}

void VlRandomizer::hard(std::string&& constraint) {
    m_constraints.emplace_back(std::move(constraint));
}

void VlRandomizer::clear() { m_constraints.clear(); }

#ifdef VL_DEBUG
void VlRandomizer::dump() const {
    for (const auto& var : m_vars) {
        VL_PRINTF("Variable (%d): %s\n", var.second->width(), var.second->name());
    }
    for (const std::string& c : m_constraints) VL_PRINTF("Constraint: %s\n", c.c_str());
}
#endif
