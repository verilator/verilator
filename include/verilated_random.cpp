// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2001-2026 Wilson Snyder
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

#include <cassert>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <streambuf>
#include <tuple>

// Diversity (scalar rand vars): tie each free bit to a random target via a
//   boolean assumption literal, then force the bits with (check-sat-assuming).
//   If UNSAT, (get-unsat-assumptions) names the literals clashing with the
//   feasible hard+soft base; drop one per round and recheck until SAT, which
//   keeps the maximal set of bits compatible with the constraints. Only these
//   private literals are assumed (never user constraints), and assumptions are
//   ephemeral, so hard/soft/randc semantics are untouched and rounds need no
//   push/pop or re-asserting. The surviving assumptions steer each free bit
//   from the random target, spreading a wide range uniformly (fixing the
//   boundary bias under `value < (1<<N)`, issue #7563) while keeping run-to-run
//   diversity on tightly coupled bits. Array/queue rand vars skip pinning
//   (per-element ranges aren't power-of-2 boundaries) and use the XOR rounds.
#define _VL_SOLVER_HASH_LEN 1
#define _VL_SOLVER_HASH_LEN_TOTAL 4

// clang-format off
#if defined(__unix__) || defined(__unix) || (defined(__APPLE__) && defined(__MACH__))
# define _VL_SOLVER_PIPE  // Allow pipe SMT solving.  Needs fork()
#endif

#ifdef _VL_SOLVER_PIPE
# include <sys/wait.h>
# include <csignal>
# include <fcntl.h>
#endif

#if defined(_WIN32) || defined(__MINGW32__)
# include <io.h>  // open, read, write, close
#endif
// clang-format on

class VlRProcess final : private std::streambuf, public std::iostream {
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

    bool m_logTried = false;  // Log file name looked up, at the first start
    std::unique_ptr<std::ofstream> m_logfp;  // Log file stream
    uint64_t m_logLastTime = ~0ULL;  // Last timestamp for logfile

public:
    typedef std::streambuf::traits_type traits_type;

protected:
    int overflow(int c = traits_type::eof()) override {
        const char c2 = static_cast<char>(c);
        if (pbase() == pptr()) return 0;
        const size_t size = pptr() - pbase();
        log("  ", std::string(pbase(), size));
        const ssize_t n = ::write(m_writeFd, pbase(), size);
        if (VL_UNLIKELY(n == -1)) perror("write");
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
        const ssize_t n = ::read(m_readFd, m_readBuf, sizeof(m_readBuf));
        if (VL_UNLIKELY(n == -1)) perror("read");
        if (n <= 0) {
            wait_report();
            return traits_type::eof();
        }
        log("< ", std::string(m_readBuf, n));
        setg(m_readBuf, m_readBuf, m_readBuf + n);
        return traits_type::to_int_type(m_readBuf[0]);
    }
    int sync() override {
        overflow();
        return 0;
    }

public:
    explicit VlRProcess(const char* const* const cmd = nullptr)
        : std::streambuf{}
        , std::iostream{this}
        , m_cmd{cmd} {
        open(cmd);
    }

    // Kill and reap a solver that is still running, so no child is left behind
    void terminate() {
#ifdef _VL_SOLVER_PIPE
        if (!m_pidExited) {
            ::kill(m_pid, SIGKILL);
            waitpid(m_pid, &m_pidStatus, 0);
        }
#endif
        m_pidExited = true;
        m_pid = 0;
        closeFds();
    }

    void wait_report() {
        if (m_pidExited) return;
        bool reaped = true;
#ifdef _VL_SOLVER_PIPE
        const pid_t rc = waitpid(m_pid, &m_pidStatus, WNOHANG);
        if (rc != m_pid) m_pidStatus = 0;
        reaped = rc != 0;  // Zero means still running, so terminate() reaps it
        if (m_pidStatus) {
            std::stringstream msg;
            msg << "Subprocess command `" << m_cmd[0];
            for (const char* const* arg = m_cmd + 1; *arg; ++arg) msg << ' ' << *arg;
            msg << "' failed: ";
            if (WIFSIGNALED(m_pidStatus))
                msg << strsignal(WTERMSIG(m_pidStatus))
                    << (WCOREDUMP(m_pidStatus) ? " (core dumped)" : "");
            else if (WIFEXITED(m_pidStatus))
                msg << "exit status " << WEXITSTATUS(m_pidStatus);
            const std::string str = msg.str();
            VL_WARN_MT("", 0, "VlRProcess", str.c_str());
        }
#endif
        if (reaped) {
            m_pidExited = true;
            m_pid = 0;
        }
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
        clear();
        setp(std::begin(m_writeBuf), std::end(m_writeBuf));
        setg(m_readBuf, m_readBuf, m_readBuf);
#ifdef _VL_SOLVER_PIPE
        if (!cmd || !cmd[0]) return false;
        m_cmd = cmd;
        if (!m_logTried) {
            m_logTried = true;
            logOpen();
        }
        int fd_stdin[2];  // Can't use std::array
        int fd_stdout[2];  // Can't use std::array
        constexpr int P_RD = 0;
        constexpr int P_WR = 1;

        if (VL_UNLIKELY(pipe(fd_stdin) != 0)) {
            perror("VlRProcess::open: pipe");
            return false;
        }
        if (VL_UNLIKELY(pipe(fd_stdout) != 0)) {
            perror("VlRProcess::open: pipe");
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

        log("", "# Open: "s + cmd[0]);
        const pid_t pid = fork();
        if (VL_UNLIKELY(pid < 0)) {
            perror("VlRProcess::open: fork");
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
            close(fd_stdin[P_RD]);
            close(fd_stdout[P_RD]);
            dup2(fd_stdout[P_WR], STDOUT_FILENO);
            close(fd_stdout[P_WR]);
            execvp(cmd[0], const_cast<char* const*>(cmd));
            std::stringstream msg;
            msg << "VlRProcess::open: execvp(" << cmd[0] << ")";
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

private:
    void logOpen() {
        const std::string filename = Verilated::threadContextp()->solverLogFilename();
        if (filename.empty()) return;
        m_logfp = std::make_unique<std::ofstream>(filename);
        if (m_logfp.get() && m_logfp.get()->fail()) m_logfp = nullptr;
        if (!m_logfp) {
            const std::string msg = "%Error: Can't write '"s + filename + "'";
            VL_FATAL_MT("", 0, "", msg.c_str());
            return;
        }
        *m_logfp << "# Verilator solver log\n";
    }
    void log(const std::string& prefix, const std::string& text) {
        if (VL_LIKELY(!m_logfp.get()) || text.empty()) return;
        if (m_logLastTime != Verilated::threadContextp()->time()) {
            m_logLastTime = Verilated::threadContextp()->time();
            *m_logfp << "# [" << Verilated::threadContextp()->timeWithUnitString() << "]\n";
        }
        std::size_t startPos = 0;
        while (1) {
            const std::size_t endPos = text.find('\n', startPos);
            if (endPos == std::string::npos) break;
            *m_logfp << prefix << text.substr(startPos, endPos - startPos) << '\n';
            startPos = endPos + 1;
        }
        if (startPos < text.length()) *m_logfp << prefix << text.substr(startPos) << '\n';
    }
};

//======================================================================
// Solver reply protocol

enum class VlSolverStatus : uint8_t { SAT, UNSAT, UNKNOWN, FAIL };

static bool isSolverError(const std::string& reply) { return reply.compare(0, 6, "(error") == 0; }

// One non-blank reply line, trimmed; false once the solver stops answering
static bool readLine(std::istream& is, std::string& liner) {
    while (std::getline(is, liner)) {
        const size_t first = liner.find_first_not_of(" \t\r");
        if (first == std::string::npos) continue;
        const size_t last = liner.find_last_not_of(" \t\r");
        liner = liner.substr(first, last - first + 1);
        return true;
    }
    return false;
}

static bool scanParenDepth(const std::string& str, int& depthr, bool& inStringr) {
    for (const char c : str) {
        if (inStringr) {
            if (c == '"') inStringr = false;
        } else if (c == '"') {
            inStringr = true;
        } else if (c == '(') {
            ++depthr;
        } else if (c == ')') {
            if (depthr == 0) return false;
            --depthr;
        }
    }
    return true;
}

// Append lines until the error s-expression started in liner is paren-balanced
static void finishErrorReply(std::istream& is, std::string& liner) {
    int depth = 0;
    bool inString = false;
    if (!scanParenDepth(liner, depth, inString)) return;
    while (depth > 0) {
        std::string chunk;
        if (!readLine(is, chunk)) return;
        liner += ' ';
        liner += chunk;
        if (!scanParenDepth(chunk, depth, inString)) return;
    }
}

static void warnSolverReply(const std::string& reply) {
    static bool s_warned = false;
    if (s_warned) return;
    s_warned = true;
    const std::string msg
        = "Solver did not answer with a status, so randomize() returns 0; warned once: " + reply;
    VL_WARN_MT(__FILE__, __LINE__, "randomize", msg.c_str());
}

// Read one solver status; only a print-success echo may precede it
static VlSolverStatus readStatus(std::istream& is) {
    std::string line;
    while (readLine(is, line)) {
        if (line == "success") continue;
        if (line == "sat") return VlSolverStatus::SAT;
        if (line == "unsat") return VlSolverStatus::UNSAT;
        if (line == "unknown") {
            static bool s_warnedUnknown = false;
            if (!s_warnedUnknown) {
                s_warnedUnknown = true;
                VL_WARN_MT(__FILE__, __LINE__, "randomize",
                           "Solver returned unknown (timed out or incomplete), so randomize() "
                           "may return 0; warned once");
            }
            return VlSolverStatus::UNKNOWN;
        }
        // Consume the whole error, so the next read starts on a reply boundary
        if (isSolverError(line)) finishErrorReply(is, line);
        warnSolverReply(line);
        return VlSolverStatus::FAIL;
    }
    return VlSolverStatus::FAIL;
}

// Read one complete paren-balanced s-expression, which may span lines
static bool readSExpr(std::istream& is, std::string& outr) {
    outr.clear();
    std::string pre;
    int depth = 0;
    bool inString = false;
    char c = 0;
    while (is.get(c)) {
        if (depth == 0) {
            if (c == '(') {
                if (!pre.empty()) break;
                outr += c;
                depth = 1;
            } else if (c == '\n') {
                if (pre == "success") pre.clear();
                if (!pre.empty()) break;
            } else if (c != ' ' && c != '\t' && c != '\r') {
                pre += c;
            }
            continue;
        }
        outr += c;
        if (inString) {
            if (c == '"') inString = false;
        } else if (c == '"') {
            inString = true;
        } else if (c == '(') {
            ++depth;
        } else if (c == ')') {
            assert(depth > 0);
            if (--depth == 0) return true;
        }
    }
    return false;
}

//======================================================================
// Solver session lifecycle

// Owns the solver process; serializes transactions and replaces a solver that
// died or was left out of step with the reply stream
class VlSolverSession final {
    friend class VlRandomizer;
    friend class VlSolverTxn;
    enum class State : uint8_t { UNSTARTED, LIVE, BROKEN, DISABLED };
    static constexpr int MAX_CONSEC_FAILS = 3;

    VerilatedMutex m_mutex;  // Serializes whole solver transactions
    VlRProcess m_proc VL_GUARDED_BY(m_mutex);  // Solver subprocess and its pipes
    State m_state VL_GUARDED_BY(m_mutex) = State::UNSTARTED;
    int m_consecFails VL_GUARDED_BY(m_mutex) = 0;  // Failed transactions in a row
    bool m_dirty VL_GUARDED_BY(m_mutex) = false;  // Transaction left the pipe out of step
    std::string m_program VL_GUARDED_BY(m_mutex);  // Storage backing m_argv
    std::vector<const char*> m_argv VL_GUARDED_BY(m_mutex);  // Solver argv
    bool m_warnedRestart VL_GUARDED_BY(m_mutex) = false;

public:
    std::iostream& os() VL_REQUIRES(m_mutex) { return m_proc; }
    // The pipe may hold bytes of an abandoned reply, so replace the solver
    void abandon() VL_REQUIRES(m_mutex) { m_dirty = true; }

    // A status the runtime cannot use fails the call, but the reply itself was
    // complete, so the solver is left alone
    VlSolverStatus readStatus() VL_REQUIRES(m_mutex) { return ::readStatus(m_proc); }
    // An unreadable reply means text of it may still be queued, so it is not
    // safe to read anything more from this solver
    bool readSExpr(std::string& outr) VL_REQUIRES(m_mutex) {
        if (::readSExpr(m_proc, outr)) return true;
        abandon();
        return false;
    }

    // Start a transaction, spawning or respawning the solver as needed
    bool begin() VL_REQUIRES(m_mutex) {
        m_dirty = false;
        if (m_state == State::BROKEN) {
            if (m_consecFails >= MAX_CONSEC_FAILS) {
                m_state = State::DISABLED;
                VL_WARN_MT(__FILE__, __LINE__, "randomize",
                           "Solver failed repeatedly, so randomize() returns 0 from now on");
            } else if (!m_warnedRestart) {
                m_warnedRestart = true;
                VL_WARN_MT(__FILE__, __LINE__, "randomize",
                           "Solver died or replied unreadably, so this randomize() returned 0; "
                           "restarting it, warned once");
            }
        }
        if (m_state == State::UNSTARTED || m_state == State::BROKEN) spawn();
        return m_state == State::LIVE;
    }

    // End a transaction; a solver left out of step or dead is replaced next time
    void end() VL_REQUIRES(m_mutex) {
        bool healthy = !m_dirty && !m_proc.fail();
        if (healthy) {
            m_proc << "(reset)\n";
            m_proc.flush();
            healthy = !m_proc.fail();
        }
        if (healthy) {
            m_consecFails = 0;
        } else {
            m_proc.terminate();
            m_state = State::BROKEN;
            ++m_consecFails;
        }
        m_dirty = false;
    }

private:
    // A solver that will not start is not started again
    void spawn() VL_REQUIRES(m_mutex) {
        if (m_argv.empty()) {
            m_program = Verilated::threadContextp()->solverProgram();
            m_argv.emplace_back(&m_program[0]);
            for (char* argp = &m_program[0]; *argp; ++argp) {
                if (*argp == ' ') {
                    *argp = '\0';
                    m_argv.emplace_back(argp + 1);
                }
            }
            m_argv.emplace_back(nullptr);
        }
        m_proc.open(m_argv.data());
        m_proc << "(set-logic QF_ABV)\n";
        m_proc << "(check-sat)\n";
        m_proc << "(reset)\n";
        if (readStatus() == VlSolverStatus::SAT) {
            m_state = State::LIVE;
            m_dirty = false;
            return;
        }
        m_proc.terminate();
        m_state = State::DISABLED;
        std::stringstream msg;
        msg << "Unable to communicate with SAT solver, please check its installation or specify a "
               "different one in VERILATOR_SOLVER environment variable.\n";
        msg << " ... Tried: $";
        for (const char* const* argp = m_argv.data(); *argp; ++argp) msg << ' ' << *argp;
        msg << '\n';
        const std::string str = msg.str();
        VL_WARN_MT("", 0, "randomize", str.c_str());
    }
};

// Constructed before main(), so nothing here may touch the thread context
static VlSolverSession s_solverSession;

// One solver transaction; the caller holds the session mutex
class VlSolverTxn final {
    VlSolverSession& m_sess;
    const bool m_ok;

public:
    explicit VlSolverTxn(VlSolverSession& sess) VL_REQUIRES(sess.m_mutex)
        : m_sess{sess}
        , m_ok{sess.begin()} {}
    // Analysis cannot see through the reference member back to the caller's lock
    ~VlSolverTxn() VL_NO_THREAD_SAFETY_ANALYSIS {
        if (m_ok) m_sess.end();
    }
    bool ok() const { return m_ok; }
};

static std::string readUntilBalanced(std::istream& stream) {
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

static std::string parseNestedSelect(const std::string& nested_select_expr,
                                     std::vector<std::string>& indices) {
    std::istringstream nestedStream(nested_select_expr);
    std::string name;
    std::string idx;
    nestedStream >> name;
    if (name == "(select") {
        const std::string further_nested_expr = readUntilBalanced(nestedStream);
        name = parseNestedSelect(further_nested_expr, indices);
    }
    std::getline(nestedStream, idx, ')');
    indices.push_back(idx);
    return name;
}

//======================================================================
// VlRandomizer:: Methods

void VlRandomVar::emitGetValue(std::ostream& s) const { s << ' ' << m_name; }
void VlRandomVar::emitExtract(std::ostream& s, int i) const {
    s << " ((_ extract " << i << ' ' << i << ") " << m_name << ')';
}
void VlRandomVar::emitType(std::ostream& s) const { s << "(_ BitVec " << width() << ')'; }
// Serialize the current runtime value as an SMT-LIB binary literal. Used by
// randomize(null) to pin a var via `(assert (= var #b...))`. Binary (#b)
// rather than hex (#x) sidesteps SMT-LIB's hex-width-multiple-of-4 rule.
void VlRandomVar::emitConcreteValue(std::ostream& s) const {
    const int w = width();
    const void* const dp = datap(0);
    s << "#b";
    for (int i = w - 1; i >= 0; --i) {
        int bit = 0;
        if (w <= VL_BYTESIZE) {
            bit = (*static_cast<const CData*>(dp) >> i) & 1;
        } else if (w <= VL_SHORTSIZE) {
            bit = (*static_cast<const SData*>(dp) >> i) & 1;
        } else if (w <= VL_IDATASIZE) {
            bit = (*static_cast<const IData*>(dp) >> i) & 1;
        } else if (w <= VL_QUADSIZE) {
            bit = (*static_cast<const QData*>(dp) >> i) & 1;
        } else {
            const WDataInP wp = WDataInP::external(static_cast<const EData*>(dp));
            bit = (wp[VL_BITWORD_E(i)] >> VL_BITBIT_E(i)) & 1;
        }
        s << (bit ? '1' : '0');
    }
}
int VlRandomVar::totalWidth() const { return m_width; }
// True if val is "#b/#o/#x/#h" followed by digits legal for that base
static bool validSMTNum(const std::string& val) {
    size_t i = val.find('#');
    if (i == std::string::npos || ++i >= val.size()) return false;
    int base;
    switch (val[i++]) {
    case 'b': base = 2; break;
    case 'o': base = 8; break;
    case 'h':  // FALLTHRU
    case 'x': base = 16; break;
    default: return false;
    }
    const size_t end = val.find_last_not_of(" \t\r");
    if (end < i) return false;
    for (; i <= end; ++i) {
        const char c = val[i];
        int digit;
        if (c >= '0' && c <= '9') {
            digit = c - '0';
        } else if (c >= 'a' && c <= 'f') {
            digit = c - 'a' + 10;
        } else if (c >= 'A' && c <= 'F') {
            digit = c - 'A' + 10;
        } else {
            return false;
        }
        if (digit >= base) return false;
    }
    return true;
}

// val must have passed validSMTNum
static void parseSMTNum(int obits, WDataOutP owp, const std::string& val) {
    size_t i = val.find('#') + 1;
    switch (val[i++]) {
    case 'b': _vl_vsss_based(owp, obits, 1, &val[i], 0, val.size() - i); break;
    case 'o': _vl_vsss_based(owp, obits, 3, &val[i], 0, val.size() - i); break;
    default: _vl_vsss_based(owp, obits, 4, &val[i], 0, val.size() - i); break;
    }
}
void VlRandomVar::set(const std::string& idx, const std::string& val) const {
    VlWide<VL_WQ_WORDS_E> qowp;
    VL_SET_WQ(qowp, 0ULL);
    WDataOutP owp = qowp;
    const int obits = width();
    VlWide<VL_WQ_WORDS_E> qiwp;
    VL_SET_WQ(qiwp, 0ULL);
    if (!idx.empty()) parseSMTNum(64, qiwp, idx);
    const int nidx = qiwp[0];
    if (obits > VL_QUADSIZE) owp = WDataOutP::external(reinterpret_cast<EData*>(datap(nidx)));
    parseSMTNum(obits, owp, val);

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
}

void VlRandomizer::randomConstraint(std::ostream& os, VlRNG& rngr, int bits) {
    const IData hash = VL_RANDOM_RNG_I(rngr) & ((1 << bits) - 1);
    int varBits = 0;
    for (const auto& var : m_vars) varBits += var.second->totalWidth();
    os << "(= #b";
    for (int i = bits - 1; i >= 0; i--) os << (VL_BITISSET_I(hash, i) ? '1' : '0');
    if (bits > 1) os << " (concat";
    for (int i = 0; i < bits; ++i) {
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

size_t VlRandomizer::hashConstraints(const std::vector<std::string>& extras) const {
    size_t h = 0;
    for (const auto& c : m_constraints) {
        h ^= std::hash<std::string>{}(c) + 0x9e3779b9 + (h << 6) + (h >> 2);
    }
    for (const auto& c : extras) {
        h ^= std::hash<std::string>{}(c) + 0x9e3779b9 + (h << 6) + (h >> 2);
    }
    return h;
}

void VlRandomizer::emitRandcExclusions(std::ostream& os) const {
    for (const auto& name : m_randcVarNames) {
        const auto usedIt = m_randcUsedValues.find(name);
        if (usedIt != m_randcUsedValues.end()) {
            const int w = m_vars.at(name)->width();
            for (const uint64_t val : usedIt->second) {
                os << "(assert (not (= " << name << " (_ bv" << val << " " << w << "))))\n";
            }
        }
    }
}

static uint64_t readVarValueU64(const void* datap, int width) {
    if (width <= VL_BYTESIZE) return *static_cast<const CData*>(datap);
    if (width <= VL_SHORTSIZE) return *static_cast<const SData*>(datap);
    if (width <= VL_IDATASIZE) return *static_cast<const IData*>(datap);
    if (width <= VL_QUADSIZE) return *static_cast<const QData*>(datap);
    return 0;
}

void VlRandomizer::recordRandcValues() {
    for (const auto& name : m_randcVarNames) {
        const auto varIt = m_vars.find(name);
        if (varIt == m_vars.end()) continue;
        const VlRandomVar& var = *varIt->second;
        m_randcUsedValues[name].insert(readVarValueU64(var.datap(0), var.width()));
    }
}

bool VlRandomizer::next_check_only(VlRNG& rngr) { return nextRandomize(rngr, true); }

bool VlRandomizer::next(VlRNG& rngr) { return nextRandomize(rngr, false); }

bool VlRandomizer::nextRandomize(VlRNG& rngr, bool checkOnly) {
    if (!checkOnly && m_vars.empty() && m_unique_arrays.empty()) return true;
    if (checkOnly && m_vars.empty()) return true;  // No rand members: trivially SAT
    VlSolverSession& sess = s_solverSession;
    const VerilatedLockGuard lock{sess.m_mutex};
    m_checkOnly = checkOnly;
    const std::vector<std::string> uniqueExprs = buildUniqueExprs();

    // Randc exclusion-based cycling: exclude previously used values per randc var.
    // When solver returns unsat (all values exhausted), clear history for new cycle.
    if (!m_randcVarNames.empty()) {
        const size_t currentHash = hashConstraints(uniqueExprs);
        // Invalidate history if constraints changed (e.g., constraint_mode toggled)
        if (currentHash != m_randcConstraintHash) {
            m_randcUsedValues.clear();
            m_randcConstraintHash = currentHash;
        }
    }

    // Pinned vars make phase ordering moot; skip phased path in check-only.
    bool result;
    if (!m_checkOnly && !m_solveBefore.empty()) {
        result = nextPhased(rngr, sess, uniqueExprs);
    } else {
        result = nextFlat(rngr, sess, uniqueExprs);
    }
    m_checkOnly = false;
    return result;
}

std::vector<std::string> VlRandomizer::buildUniqueExprs() const {
    std::vector<std::string> exprs;
    if (m_unique_arrays.empty()) return exprs;
    const auto arrVarsp = std::make_shared<const ArrayInfoMap>(m_arr_vars);
    for (const std::string& baseName : m_unique_arrays) {
        const auto it = m_vars.find(baseName);
        if (it == m_vars.end()) continue;
        const VlRandomVar& var = *it->second;
        // Select the elements the array actually holds now, by their own index
        // or key, rather than by ordinal position
        var.setArrayInfo(arrVarsp);
        // 'distinct' needs at least two operands; fewer elements are trivially unique
        if (var.countMatchingElements(*arrVarsp, baseName) < 2) continue;
        std::ostringstream os;
        os << "(__Vbv (distinct ";
        var.emitGetValue(os);
        os << "))";
        exprs.push_back(os.str());
    }
    return exprs;
}

void VlRandomizer::emitDefines(std::ostream& os) const {
    os << "(define-fun __Vbv ((b Bool)) (_ BitVec 1) (ite b #b1 #b0))\n";
    os << "(define-fun __Vbool ((v (_ BitVec 1))) Bool (= #b1 v))\n";
}

void VlRandomizer::emitDeclares(std::ostream& os, bool pinCurrent) const {
    for (const auto& var : m_vars) {
        if (var.second->dimension() > 0) {
            auto arrVarsp = std::make_shared<const ArrayInfoMap>(m_arr_vars);
            var.second->setArrayInfo(arrVarsp);
        }
        os << "(declare-fun " << var.first << " () ";
        var.second->emitType(os);
        os << ")\n";
        // Pin each var to its current value
        if (pinCurrent) {
            assert(var.second->dimension() == 0);
            os << "(assert (= " << var.first << ' ';
            var.second->emitConcreteValue(os);
            os << "))\n";
        }
    }
}

void VlRandomizer::emitAsserts(std::ostream& os, const std::vector<std::string>& extras,
                               bool named) const {
    int j = 0;
    for (const std::string& constraint : m_constraints) {
        if (named) {
            os << "(assert (! (= #b1 " << constraint << ") :named cons" << j++ << "))\n";
        } else {
            os << "(assert (= #b1 " << constraint << "))\n";
        }
    }
    for (const std::string& extra : extras) {
        if (named) {
            os << "(assert (! (= #b1 " << extra << ") :named cons" << j++ << "))\n";
        } else {
            os << "(assert (= #b1 " << extra << "))\n";
        }
    }
}

bool VlRandomizer::nextFlat(VlRNG& rngr, VlSolverSession& sess,
                            const std::vector<std::string>& uniqueExprs)
    VL_REQUIRES(sess.m_mutex) {
    VlSolverTxn txn{sess};
    if (!txn.ok()) return false;
    std::iostream& os = sess.os();
    // Randc retry: if unsat due to randc exhaustion, clear history and retry once
    const bool hasRandc = !m_randcVarNames.empty();
    for (int attempt = 0; attempt < (hasRandc ? 2 : 1); ++attempt) {
        os << "(set-option :produce-models true)\n";
        // Lets the scalar pin path learn which free-bit assumptions conflict.
        os << "(set-option :produce-unsat-assumptions true)\n";
        os << "(set-logic QF_ABV)\n";
        emitDefines(os);
        emitDeclares(os, m_checkOnly);
        emitAsserts(os, uniqueExprs, false);

        // randc exclusions vs. a pinned current value would make every check
        // trivially UNSAT after the first cycle.
        if (!m_checkOnly) emitRandcExclusions(os);

        relaxSoftConstraints(sess);
        os << "(check-sat)\n";
        const VlSolverStatus status = sess.readStatus();

        if (status != VlSolverStatus::SAT) {
            if (status != VlSolverStatus::UNSAT) return false;
            os << "(reset)\n";
            // If randc vars have used values, this may be cycle exhaustion - retry
            if (hasRandc && !m_randcUsedValues.empty() && attempt == 0) {
                m_randcUsedValues.clear();
                continue;  // Retry without exclusions
            }
            // Skip the unsat-core path in check-only: it re-declares vars
            // without pinning, so the solver's free assignment would clobber
            // user state.
            if (m_checkOnly) return false;
            // Genuine unsat: report via unsat-core
            reportUnsatSetup(sess, uniqueExprs);
            return false;
        }
        if (!applyModel(sess)) return false;

        if (!m_checkOnly) {
            solveDiversity(rngr, sess);
            // Check-only must not advance randc cycle state.
            recordRandcValues();
        }
        return true;
    }
    return false;  // Should not reach here
}

void VlRandomizer::solveDiversity(VlRNG& rngr, VlSolverSession& sess) VL_REQUIRES(sess.m_mutex) {
    bool hasArray = false;
    for (const auto& var : m_vars) {
        if (var.second->dimension() > 0) {
            hasArray = true;
            break;
        }
    }
    if (hasArray) {
        solveDiversityXor(rngr, sess);
    } else {
        solveDiversityPins(rngr, sess);
    }
}

void VlRandomizer::solveDiversityPins(VlRNG& rngr, VlSolverSession& sess)
    VL_REQUIRES(sess.m_mutex) {
    std::iostream& os = sess.os();
    // Tie each free bit to a random target via an assumption literal;
    // drop one conflicting literal per round until compatible
    int npins = 0;
    for (const auto& var : m_vars) {
        const int w = var.second->totalWidth();
        for (int b = 0; b < w; ++b) {
            const bool target = (VL_RANDOM_RNG_I(rngr) & 1);
            os << "(declare-fun a" << npins << " () Bool)\n";
            os << "(assert (= a" << npins << " (=";
            var.second->emitExtract(os, b);
            os << " #b" << (target ? '1' : '0') << ")))\n";
            ++npins;
        }
    }
    std::vector<bool> dropped(npins, false);
    for (int round = 0; round <= npins; ++round) {
        os << "(check-sat-assuming (";
        for (int k = 0; k < npins; ++k) {
            if (!dropped[k]) os << " a" << k;
        }
        os << "))\n";
        const VlSolverStatus status = sess.readStatus();
        if (status == VlSolverStatus::SAT) {
            applyModel(sess);
            return;
        }
        // Unknown or failure: the base solution already written stands
        if (status != VlSolverStatus::UNSAT) return;
        // get-unsat-assumptions only echoes still-active literals,
        // so the first in-range index is a live conflicting bit.
        const std::vector<int> core = readUnsatAssumptions(sess);
        bool droppedOne = false;
        for (const int idx : core) {
            if (idx < npins) {
                dropped[idx] = true;
                droppedOne = true;
                break;
            }
        }
        if (!droppedOne) return;
    }
}

void VlRandomizer::solveDiversityXor(VlRNG& rngr, VlSolverSession& sess)
    VL_REQUIRES(sess.m_mutex) {
    std::iostream& os = sess.os();
    for (int i = 0; i < _VL_SOLVER_HASH_LEN_TOTAL; ++i) {
        os << "(assert ";
        randomConstraint(os, rngr, _VL_SOLVER_HASH_LEN);
        os << ")\n";
        os << "\n(check-sat)\n";
        if (sess.readStatus() != VlSolverStatus::SAT) break;
        if (!applyModel(sess)) break;
    }
}

// Re-add softs highest-priority first, dropping incompatible ones.
void VlRandomizer::relaxSoftConstraints(VlSolverSession& sess) VL_REQUIRES(sess.m_mutex) {
    if (m_softConstraints.empty()) return;
    std::iostream& os = sess.os();
    os << "(push 1)\n";
    for (const auto& s : m_softConstraints) os << "(assert (= #b1 " << s << "))\n";
    os << "(check-sat)\n";
    const VlSolverStatus status = sess.readStatus();
    if (status == VlSolverStatus::SAT || status == VlSolverStatus::FAIL) return;
    os << "(pop 1)\n";
    for (auto it = m_softConstraints.rbegin(); it != m_softConstraints.rend(); ++it) {
        os << "(push 1)\n";
        os << "(assert (= #b1 " << *it << "))\n";
        os << "(check-sat)\n";
        const VlSolverStatus probe = sess.readStatus();
        if (probe == VlSolverStatus::FAIL) return;
        if (probe != VlSolverStatus::SAT) os << "(pop 1)\n";
    }
}

// Every complete run of digits in the reply, in order
static std::vector<int> scanIntRuns(const std::string& reply) {
    std::vector<int> idxs;
    std::string num;
    for (const char c : reply) {
        // Cap the run so a garbled reply cannot overflow std::stoi
        if (std::isdigit(static_cast<unsigned char>(c)) && num.size() < 9) {
            num += c;
        } else if (!num.empty()) {
            idxs.push_back(std::stoi(num));
            num.clear();
        }
    }
    if (!num.empty()) idxs.push_back(std::stoi(num));
    return idxs;
}

std::vector<int> VlRandomizer::readUnsatAssumptions(VlSolverSession& sess)
    VL_REQUIRES(sess.m_mutex) {
    sess.os() << "(get-unsat-assumptions)\n";
    std::string reply;
    if (!sess.readSExpr(reply)) return {};
    if (isSolverError(reply)) {
        warnSolverReply(reply);
        return {};
    }
    // The response lists only "a<N>" literals; collect each full integer run.
    return scanIntRuns(reply);
}

// Re-solve with named asserts so an unsat core can name the failing constraints
void VlRandomizer::reportUnsatSetup(VlSolverSession& sess,
                                    const std::vector<std::string>& uniqueExprs)
    VL_REQUIRES(sess.m_mutex) {
    std::iostream& os = sess.os();
    os << "(set-option :produce-unsat-cores true)\n";
    os << "(set-logic QF_ABV)\n";
    emitDefines(os);
    emitDeclares(os, false);
    emitAsserts(os, uniqueExprs, true);
    os << "(check-sat)\n";
    if (sess.readStatus() == VlSolverStatus::UNSAT) reportUnsatCore(sess);
}

void VlRandomizer::reportUnsatCore(VlSolverSession& sess) VL_REQUIRES(sess.m_mutex) {
    sess.os() << "(get-unsat-core)\n";
    std::string reply;
    if (!sess.readSExpr(reply)) return;
    if (isSolverError(reply)) {
        warnSolverReply(reply);
        return;
    }
    const std::vector<int> numbers = scanIntRuns(reply);
    if (Verilated::threadContextp()->warnUnsatConstr()) {
        for (const int n : numbers) {
            if (static_cast<size_t>(n) < m_constraints_line.size()) {
                const std::string& constraint_info = m_constraints_line[n];
                // Parse "filename:linenum   source" format, parts optional
                std::string filename;
                int linenum = 0;
                std::string source = constraint_info;
                const size_t colon_pos = constraint_info.find(':');
                if (colon_pos != std::string::npos) {
                    filename = constraint_info.substr(0, colon_pos);
                    const size_t space_pos = constraint_info.find("   ", colon_pos);
                    const size_t num_end
                        = space_pos == std::string::npos ? constraint_info.size() : space_pos;
                    linenum = std::atoi(
                        constraint_info.substr(colon_pos + 1, num_end - colon_pos - 1).c_str());
                    source = space_pos == std::string::npos
                                 ? ""
                                 : constraint_info.substr(space_pos + 3);
                }
                std::string msg = "UNSATCONSTR: Unsatisfied constraint";
                const size_t start = source.find_first_not_of(" \t");
                if (start != std::string::npos) msg += ": '" + source.substr(start) + "'";
                VL_WARN_MT(filename.c_str(), linenum, "", msg.c_str());
            }
        }
    }
}

bool VlRandomizer::applyModel(VlSolverSession& sess) VL_REQUIRES(sess.m_mutex) {
    std::iostream& os = sess.os();
    size_t requested = 0;
    std::stringstream getValueStr;
    for (const auto& var : m_vars) {
        if (var.second->dimension() > 0) {
            auto arrVarsp = std::make_shared<const ArrayInfoMap>(m_arr_vars);
            var.second->setArrayInfo(arrVarsp);
            requested += var.second->countMatchingElements(m_arr_vars, var.second->name());
        } else {
            ++requested;
        }
        var.second->emitGetValue(getValueStr);
    }
    if (getValueStr.str() == "") {
        // Mark as m_checkOnly to skip generation of any subsequent solver calls
        m_checkOnly = true;
        return true;
    }
    os << "(get-value (" << getValueStr.str() << "))\n";
    std::string reply;
    if (!sess.readSExpr(reply)) return false;
    if (isSolverError(reply)) {
        warnSolverReply(reply);
        return false;
    }
    std::istringstream is{reply};
    return parseModel(is, requested);
}

bool VlRandomizer::parseModel(std::istream& is, size_t requested) {
    // Quasi-parse S-expression of the form ((x #xVALUE) (y #bVALUE) (z #xVALUE))
    char c = 0;
    is >> c;  // The '(' opening the readSExpr-balanced reply
    // Stage writes; commit only after the whole reply parses so failure keeps prior values
    std::vector<std::tuple<const VlRandomVar*, std::string, std::string>> staged;
    // Every requested term must come back exactly once, whether or not it is written
    std::set<std::string> answered;
    while (true) {
        if (VL_UNCOVERABLE(!(is >> c))) return false;  // Balanced reply breaks at ')' first
        if (c == ')') break;
        if (c != '(') {
            VL_WARN_MT(__FILE__, __LINE__, "randomize",
                       "Internal: Unable to parse solver's response: invalid S-expression");
            return false;
        }
        std::string name;
        std::string idx;
        std::string value;
        std::vector<std::string> indices;
        is >> name;
        indices.clear();
        if (name == "(select") {
            const std::string selectExpr = readUntilBalanced(is);
            name = parseNestedSelect(selectExpr, indices);
        }
        std::getline(is, value, ')');
        const auto it = m_vars.find(name);
        if (it == m_vars.end()) {
            VL_WARN_MT(__FILE__, __LINE__, "randomize",
                       "Internal: Unable to parse solver's response: unknown variable");
            return false;
        }
        const VlRandomVar& varr = *it->second;
        std::string key = name;
        for (const auto& index : indices) key += index;
        if (!answered.insert(key).second) {
            VL_WARN_MT(__FILE__, __LINE__, "randomize",
                       "Internal: Unable to parse solver's response: repeated variable");
            return false;
        }
        if (!varr.randModeIdxNone()) {
            // Static rand vars have their rand_mode in a class-package shared queue,
            // not the per-instance one.
            const VlQueue<CData>* const modep
                = m_staticVars.count(name) ? m_static_randmodep : m_randmodep;
            if (modep && !modep->at(varr.randModeIdx())) continue;
        }
        if (m_disabledVars.count(name)) continue;
        if (!indices.empty()) {
            std::ostringstream oss;
            oss << varr.name();
            for (const auto& hex_index : indices) {
                const size_t start = hex_index.find_first_not_of(" ");
                if (start == std::string::npos || hex_index.substr(start, 2) != "#x") {
                    VL_FATAL_MT(__FILE__, __LINE__, "randomize",
                                "hex_index contains invalid format");
                    continue;
                }
                std::string trimmed_hex = hex_index.substr(start + 2);
                if (!validSMTNum(hex_index)) {
                    VL_WARN_MT(__FILE__, __LINE__, "randomize",
                               "Internal: Unable to parse solver's response: invalid array index");
                    return false;
                }

                if (trimmed_hex.size() <= 8) {  // Small numbers: <= 32 bits
                    // Convert to decimal and output directly
                    oss << "[" << std::to_string(std::stoll(trimmed_hex, nullptr, 16)) << "]";
                } else {  // Large numbers: > 32 bits
                    // Trim leading zeros and handle empty case
                    trimmed_hex.erase(0, trimmed_hex.find_first_not_of('0'));
                    oss << "[" << (trimmed_hex.empty() ? "0" : trimmed_hex) << "]";
                }
            }
            const std::string indexed_name = oss.str();

            const auto iti = std::find_if(m_arr_vars.begin(), m_arr_vars.end(),
                                          [&indexed_name](const auto& entry) {
                                              return entry.second->m_name == indexed_name;
                                          });
            if (iti != m_arr_vars.end()) {
                std::ostringstream ss;
                ss << "#x" << std::hex << std::setw(8) << std::setfill('0')
                   << iti->second->m_index;
                idx = ss.str();
            } else {
                VL_FATAL_MT(__FILE__, __LINE__, "randomize",
                            "indexed_name not found in m_arr_vars");
            }
        }
        // Reject before any commit, so a bad value later in the reply cannot
        // leave earlier ones written
        if (!validSMTNum(value)) {
            VL_WARN_MT(__FILE__, __LINE__, "randomize",
                       "Internal: Unable to parse solver's response: invalid value");
            return false;
        }
        staged.emplace_back(&varr, idx, value);
    }
    if (answered.size() != requested) {
        VL_WARN_MT(__FILE__, __LINE__, "randomize",
                   "Internal: Unable to parse solver's response: incomplete model");
        return false;
    }
    for (const auto& entry : staged)
        std::get<0>(entry)->set(std::get<1>(entry), std::get<2>(entry));
    return true;
}

void VlRandomizer::hard(std::string&& constraint, const char* filename, uint32_t linenum,
                        const char* source) {
    m_constraints.emplace_back(std::move(constraint));
    // Format constraint location: "filename:linenum   source"
    if (filename[0] != '\0' || source[0] != '\0') {
        std::string line;
        if (filename[0] != '\0') {
            line = std::string(filename) + ":" + std::to_string(linenum);
            if (source[0] != '\0') line += "   " + std::string(source);
        } else {
            line = source;
        }
        m_constraints_line.emplace_back(std::move(line));
    }
}

void VlRandomizer::soft(std::string&& constraint, const char* /*filename*/, uint32_t /*linenum*/,
                        const char* /*source*/) {
    m_softConstraints.emplace_back(std::move(constraint));
}

void VlRandomizer::disable_soft(const std::string& varName) {
    // IEEE 1800-2023 18.5.13: Remove all soft constraints referencing the variable
    m_softConstraints.erase(
        std::remove_if(m_softConstraints.begin(), m_softConstraints.end(),
                       [&](const std::string& c) { return c.find(varName) != std::string::npos; }),
        m_softConstraints.end());
}

void VlRandomizer::clearConstraints() {
    m_constraints.clear();
    m_constraints_line.clear();
    m_solveBefore.clear();
    m_softConstraints.clear();
    m_unique_arrays.clear();  // Re-registered by constraint setup
    // Keep m_vars for class member randomization
}

void VlRandomizer::clearAll() {
    m_constraints.clear();
    m_softConstraints.clear();
    m_vars.clear();
    m_randcVarNames.clear();
    m_randcUsedValues.clear();
    m_randcConstraintHash = 0;
}

void VlRandomizer::markRandc(const char* name) { m_randcVarNames.insert(name); }
void VlRandomizer::markRandc(const std::string& name) { m_randcVarNames.insert(name); }

void VlRandomizer::solveBefore(const std::string& beforeName, const std::string& afterName) {
    m_solveBefore.emplace_back(beforeName, afterName);
}

bool VlRandomizer::buildSolveLayers(std::vector<std::vector<std::string>>& layersr) {
    std::map<std::string, std::set<std::string>> graph;
    std::map<std::string, int> inDegree;
    std::set<std::string> solveBeforeVars;

    for (const auto& pair : m_solveBefore) {
        const std::string& before = pair.first;
        const std::string& after = pair.second;
        // Only consider variables that are actually registered
        if (m_vars.find(before) == m_vars.end() || m_vars.find(after) == m_vars.end()) continue;
        graph[before].insert(after);
        solveBeforeVars.insert(before);
        solveBeforeVars.insert(after);
        if (inDegree.find(before) == inDegree.end()) inDegree[before] = 0;
        if (inDegree.find(after) == inDegree.end()) inDegree[after] = 0;
    }

    // "solve x before y": edge x -> y, in-degree of y increases
    for (const auto& entry : graph) {
        for (const auto& to : entry.second) { inDegree[to]++; }
    }

    std::set<std::string> remaining = solveBeforeVars;
    while (!remaining.empty()) {
        std::vector<std::string> currentLayer;
        for (const auto& var : remaining) {
            if (inDegree[var] == 0) currentLayer.push_back(var);
        }
        if (currentLayer.empty()) {
            VL_WARN_MT("", 0, "randomize", "Circular dependency in solve-before constraints");
            return false;
        }
        std::sort(currentLayer.begin(), currentLayer.end());
        for (const auto& var : currentLayer) {
            remaining.erase(var);
            if (graph.count(var)) {
                for (const auto& to : graph[var]) { inDegree[to]--; }
            }
        }
        layersr.push_back(std::move(currentLayer));
    }
    return true;
}

const char* VlRandomizer::phasedLogic() const {
    for (const auto& var : m_vars) {
        if (var.second->dimension() == 0) continue;
        if (!var.second->hasMatchingElements(m_arr_vars, var.second->name())) return "ALL";
    }
    return "QF_ABV";
}

bool VlRandomizer::nextPhased(VlRNG& rngr, VlSolverSession& sess,
                              const std::vector<std::string>& uniqueExprs)
    VL_REQUIRES(sess.m_mutex) {
    // Solve layer by layer with ALL constraints, pinning earlier layers
    std::vector<std::vector<std::string>> layers;
    if (!buildSolveLayers(layers)) return false;

    // One layer: all solve_before vars are independent, no ordering required
    if (layers.size() <= 1) return nextFlat(rngr, sess, uniqueExprs);

    VlSolverTxn txn{sess};
    if (!txn.ok()) return false;
    // Retry once with the randc cycle cleared, as nextFlat does
    bool exhausted = false;
    if (solvePhases(rngr, sess, layers, uniqueExprs, exhausted)) return true;
    if (!exhausted) return false;
    m_randcUsedValues.clear();
    sess.os() << "(reset)\n";
    return solvePhases(rngr, sess, layers, uniqueExprs, exhausted);
}

bool VlRandomizer::solvePhases(VlRNG& rngr, VlSolverSession& sess,
                               const std::vector<std::vector<std::string>>& layers,
                               const std::vector<std::string>& uniqueExprs, bool& exhaustedr)
    VL_REQUIRES(sess.m_mutex) {
    std::iostream& os = sess.os();
    std::map<std::string, std::string> solvedValues;  // varName -> SMT value literal
    const char* const logicp = phasedLogic();

    for (size_t phase = 0; phase < layers.size(); phase++) {
        const bool isFinalPhase = (phase == layers.size() - 1);

        os << "(set-option :produce-models true)\n";
        os << "(set-logic " << logicp << ")\n";
        emitDefines(os);
        emitDeclares(os, false);

        for (const auto& entry : solvedValues) {
            os << "(assert (= " << entry.first << " " << entry.second << "))\n";
        }
        emitAsserts(os, uniqueExprs, false);

        // Randc: exclude previously used values
        emitRandcExclusions(os);

        // Soft constraints participate in every phase, priority-ordered.
        relaxSoftConstraints(sess);

        // Initial check-sat WITHOUT diversity (guaranteed sat if constraints are consistent)
        os << "(check-sat)\n";
        const VlSolverStatus status = sess.readStatus();
        if (status != VlSolverStatus::SAT) {
            // Only exhausted randc values are worth a retry; a lost solver is not
            if (status == VlSolverStatus::UNSAT) exhaustedr = !m_randcUsedValues.empty();
            return false;
        }

        if (isFinalPhase) {
            if (!applyModel(sess)) return false;
            solveDiversityXor(rngr, sess);
            // Record solved randc values for future exclusion
            recordRandcValues();
        } else {
            if (!solvePhaseValues(sess, rngr, layers[phase], solvedValues)) return false;
            os << "(reset)\n";
        }
    }

    return true;
}

// Intermediate phase: extract this layer's values, then try one diversity round
bool VlRandomizer::solvePhaseValues(VlSolverSession& sess, VlRNG& rngr,
                                    const std::vector<std::string>& layerVars,
                                    std::map<std::string, std::string>& solvedValuesr)
    VL_REQUIRES(sess.m_mutex) {
    std::iostream& os = sess.os();
    const auto emitGetValueCmd = [&]() {
        os << "(get-value (";
        for (const auto& varName : layerVars) {
            const auto it = m_vars.find(varName);
            if (it->second->dimension() > 0) {
                auto arrVarsp = std::make_shared<const ArrayInfoMap>(m_arr_vars);
                it->second->setArrayInfo(arrVarsp);
                // Enumerable arrays: query each element for a QF_ABV-safe pin.
                if (it->second->hasMatchingElements(m_arr_vars, it->second->name())) {
                    it->second->emitGetValue(os);
                    continue;
                }
            }
            os << varName << " ";
        }
        os << "))\n";
    };
    // Get baseline values (deterministic, always valid)
    emitGetValueCmd();
    if (!readPhaseValues(sess, solvedValuesr)) return false;

    // Try diversity: add random constraint, re-check. If sat, get
    // updated (more diverse) values. If unsat, keep baseline values.
    os << "(assert ";
    randomConstraint(os, rngr, _VL_SOLVER_HASH_LEN);
    os << ")\n";
    os << "(check-sat)\n";
    if (sess.readStatus() == VlSolverStatus::SAT) {
        emitGetValueCmd();
        (void)readPhaseValues(sess, solvedValuesr);
    }
    return true;
}

bool VlRandomizer::readPhaseValues(VlSolverSession& sess,
                                   std::map<std::string, std::string>& solvedValuesr)
    VL_REQUIRES(sess.m_mutex) {
    std::string reply;
    if (!sess.readSExpr(reply)) return false;
    if (isSolverError(reply)) {
        warnSolverReply(reply);
        return false;
    }
    std::istringstream is{reply};
    return parsePhaseValues(is, solvedValuesr);
}

bool VlRandomizer::parsePhaseValues(std::istream& is,
                                    std::map<std::string, std::string>& solvedValuesr) {
    // Parse ((name value) ...): one paren-depth counter drives every match.
    char c = 0;
    is >> c;  // outer '('
    if (c != '(') return false;
    int depth = 1;
    std::string tokens[2];
    std::string cur;
    int fields = 0;
    const auto flush = [&]() {
        if (cur.empty()) return;
        if (fields < 2) tokens[fields] = cur;
        ++fields;
        cur.clear();
    };
    while (depth > 0 && is.get(c)) {
        if (c == '(') {
            ++depth;
            if (depth >= 3) cur += c;
        } else if (c == ')') {
            --depth;
            if (depth >= 2) {
                cur += c;
            } else if (depth == 1) {
                flush();
                if (fields == 2) solvedValuesr[tokens[0]] = tokens[1];
                fields = 0;
            }
        } else if (c == ' ' || c == '\t' || c == '\n' || c == '\r') {
            if (depth >= 3) {
                cur += c;
            } else {
                flush();
            }
        } else {
            cur += c;
        }
    }
    return true;
}

#ifdef VL_DEBUG
void VlRandomizer::dump() const {
    for (const auto& var : m_vars) {
        VL_PRINTF("Variable (%d): %s\n", var.second->width(), var.second->name().c_str());
    }
    for (const std::string& c : m_constraints) VL_PRINTF("Constraint: %s\n", c.c_str());
}
#endif
