// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Os-specific function wrapper
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

// clang-format off
#if defined(_WIN32) || defined(__MINGW32__)
# ifndef PSAPI_VERSION
#  define PSAPI_VERSION 1  // Needed for compatibility with Windows 7
# endif
#endif
#if defined(__MINGW32__)
# define MINGW_HAS_SECURE_API 1  // Needed to expose a "secure" POSIX-like API
#endif
// clang-format on

#include "config_build.h"
#include "verilatedos.h"

// Limited V3 headers here - this is a base class for Vlc etc
#include "V3Os.h"
#include "V3String.h"

#ifndef V3ERROR_NO_GLOBAL_
#include "V3Global.h"
VL_DEFINE_DEBUG_FUNCTIONS;
#endif

#include <array>
#include <cerrno>
#include <climits>  // PATH_MAX (especially on FreeBSD)
#include <cstdarg>
#include <cstdint>
#include <dirent.h>
#include <fstream>
#include <memory>

#include <sys/stat.h>
#include <sys/types.h>

// clang-format off
#if defined(_WIN32) || defined(__MINGW32__)
# include <windows.h>   // LONG for bcrypt.h on MINGW
# include <bcrypt.h>  // BCryptGenRandom
# include <chrono>
# include <direct.h>  // mkdir
# include <psapi.h>   // GetProcessMemoryInfo
# include <thread>
// These macros taken from gdbsupport/gdb_wait.h in binutils-gdb
# ifndef WIFEXITED
#  ifdef __MINGW32__
#   define WIFEXITED(w) (((w) & 0xC0000000) == 0)
#   define WEXITSTATUS(w) ((w) & ~0xC0000000)
#  else
#   define WIFEXITED(w) (((w) & 0377) == 0)
#   define WEXITSTATUS(w) (((w) >> 8) & 0377)
#  endif
# endif
#else
# include <sys/time.h>
# include <sys/wait.h>  // Needed on FreeBSD for WIFEXITED
# include <unistd.h>  // usleep
#endif

#if defined(__linux__)
# include <atomic>
# include <csignal>
# include <fcntl.h>
# include <sys/syscall.h>
#endif
// clang-format on

//######################################################################
// Environment

string V3Os::getenvStr(const string& envvar, const string& defaultValue) {
#if defined(_MSC_VER)
    // Note: MinGW does not offer _dupenv_s
    const char* const envvalue = nullptr;
    _dupenv_s(&envvalue, nullptr, envvar.c_str());
    if (envvalue != nullptr) {
        const std::string result{envvalue};
        free(envvalue);
        return result;
    } else {
        return defaultValue;
    }
#else
    if (const char* const envvalue = getenv(envvar.c_str())) {
        return envvalue;
    } else {
        return defaultValue;
    }
#endif
}

void V3Os::setenvStr(const string& envvar, const string& value, const string& why) {
    if (why != "") {
        UINFO(1, "export " << envvar << "=" << value << " # " << why << endl);
    } else {
        UINFO(1, "export " << envvar << "=" << value << endl);
    }
#if defined(_WIN32) || defined(__MINGW32__)
    _putenv_s(envvar.c_str(), value.c_str());
#elif defined(_BSD_SOURCE) || (defined(_POSIX_C_SOURCE) && _POSIX_C_SOURCE >= 200112L)
    setenv(envvar.c_str(), value.c_str(), true);
#else
    // setenv() replaced by putenv() in Solaris environment. Prototype is different
    // putenv() requires NAME=VALUE format
    const string vareq = envvar + "=" + value;
    putenv(const_cast<char*>(vareq.c_str()));
#endif
}

//######################################################################
// Generic filename utilities

string V3Os::filenameFromDirBase(const string& dir, const string& basename) {
    // Don't return ./{filename} because if filename was absolute, that makes it relative
    if (dir == ".") {
        return basename;
    } else {
        return dir + "/" + basename;
    }
}

string V3Os::filenameDir(const string& filename) {
    string::size_type pos;
    if ((pos = filename.rfind('/')) != string::npos) {
        return filename.substr(0, pos);
    } else {
        return ".";
    }
}

string V3Os::filenameNonDir(const string& filename) {
    string::size_type pos;
    if ((pos = filename.rfind('/')) != string::npos) {
        return filename.substr(pos + 1);
    } else {
        return filename;
    }
}

string V3Os::filenameNonExt(const string& filename) {
    string base = filenameNonDir(filename);
    string::size_type pos;
    if ((pos = base.find('.')) != string::npos) base.erase(pos);
    return base;
}

string V3Os::filenameSubstitute(const string& filename) {
    string out;
    enum : uint8_t { NONE, PAREN, CURLY } brackets = NONE;
    for (string::size_type pos = 0; pos < filename.length(); ++pos) {
        if ((filename[pos] == '$') && (pos + 1 < filename.length())) {
            switch (filename[pos + 1]) {
            case '{': brackets = CURLY; break;
            case '(': brackets = PAREN; break;
            default: brackets = NONE; break;
            }
            if (brackets != NONE) pos = pos + 1;
            string::size_type endpos = pos + 1;
            while (((endpos + 1) < filename.length())
                   && (((brackets == NONE)
                        && (isalnum(filename[endpos + 1]) || filename[endpos + 1] == '_'))
                       || ((brackets == CURLY) && (filename[endpos + 1] != '}'))
                       || ((brackets == PAREN) && (filename[endpos + 1] != ')'))))
                ++endpos;
            // Catch bracket errors
            if (((brackets == CURLY) && (filename[endpos + 1] != '}'))
                || ((brackets == PAREN) && (filename[endpos + 1] != ')'))) {
                v3fatal("Unmatched brackets in variable substitution in file: " + filename);
            }
            const string envvar = filename.substr(pos + 1, endpos - pos);
            string envvalue;
            if (!envvar.empty()) envvalue = getenvStr(envvar, "");
            if (!envvalue.empty()) {
                out += envvalue;
                if (brackets == NONE) {
                    pos = endpos;
                } else {
                    pos = endpos + 1;
                }
            } else {
                out += filename[pos];  // *pos == '$'
            }
        } else {
            out += filename[pos];
        }
    }
    return out;
}

string V3Os::filenameRealPath(const string& filename) {
    // Get rid of all the ../ behavior in the middle of the paths.
    // If there is a ../ that goes down from the 'root' of this path it is preserved.
    char retpath[PATH_MAX];
    if (
#if defined(_WIN32) || defined(__MINGW32__)
        _fullpath(retpath, filename.c_str(), PATH_MAX)
#else
        realpath(filename.c_str(), retpath)
#endif
    ) {
        return std::string{retpath};
    } else {
        return filename;
    }
}

bool V3Os::filenameIsRel(const string& filename) {
    return (filename.length() > 0 && filename[0] != '/');
}

//######################################################################
// File utilities

string V3Os::getline(std::istream& is, char delim) {
    string line;
#if defined(__CYGWIN__)  // Work around buggy implementation of getline
    char buf[65536];
    is.getline(buf, 65535, delim);
    line = buf;
#else
    std::getline(is, line, delim);
#endif
    return line;
}

//######################################################################
// Directory utilities

void V3Os::createDir(const string& dirname) {
#if defined(_WIN32) || defined(__MINGW32__)
    _mkdir(dirname.c_str());
#else
    mkdir(dirname.c_str(), 0777);
#endif
}

void V3Os::unlinkRegexp(const string& dir, const string& regexp) {
    if (DIR* const dirp = opendir(dir.c_str())) {
        while (struct dirent* const direntp = readdir(dirp)) {
            if (VString::wildmatch(direntp->d_name, regexp.c_str())) {
                const string fullname = dir + "/" + std::string{direntp->d_name};
#if defined(_WIN32) || defined(__MINGW32__)
                _unlink(fullname.c_str());
#else
                unlink(fullname.c_str());
#endif
            }
        }
        closedir(dirp);
    }
}

//######################################################################
// METHODS (random)

uint64_t V3Os::rand64(std::array<uint64_t, 2>& stater) {
    // Xoroshiro128+ algorithm
    const uint64_t result = stater[0] + stater[1];
    stater[1] ^= stater[0];
    stater[0] = (((stater[0] << 55) | (stater[0] >> 9)) ^ stater[1] ^ (stater[1] << 14));
    stater[1] = (stater[1] << 36) | (stater[1] >> 28);
    return result;
}

string V3Os::trueRandom(size_t size) {
    string result(size, '\xFF');
    char* const data = const_cast<char*>(result.data());
    // Note: std::string.data() returns a non-const Char* from C++17 onwards.
    // For pre-C++17, this cast is OK in practice, even though it's UB.
#if defined(_WIN32) || defined(__MINGW32__)
    const NTSTATUS hr = BCryptGenRandom(nullptr, reinterpret_cast<BYTE*>(data), size,
                                        BCRYPT_USE_SYSTEM_PREFERRED_RNG);
    if (!BCRYPT_SUCCESS(hr)) v3fatal("Could not acquire random data.");
#else
    std::ifstream is{"/dev/urandom", std::ios::in | std::ios::binary};
    // This read uses the size of the buffer.
    // Flawfinder: ignore
    if (VL_UNCOVERABLE(!is.read(data, size))) {
        v3fatal("Could not open /dev/urandom, no source of randomness. "  // LCOV_EXCL_LINE
                "Try specifying a key instead.");
    }
#endif
    return result;
}

//######################################################################
// METHODS (performance)

uint64_t V3Os::timeUsecs() {
#if defined(_WIN32) || defined(__MINGW32__)
    // Microseconds between 1601-01-01 00:00:00 UTC and 1970-01-01 00:00:00 UTC
    static const uint64_t EPOCH_DIFFERENCE_USECS = 11644473600000000ULL;

    FILETIME ft;  // contains number of 0.1us intervals since the beginning of 1601 UTC.
    GetSystemTimeAsFileTime(&ft);
    uint64_t us
        = ((static_cast<uint64_t>(ft.dwHighDateTime) << 32) + ft.dwLowDateTime + 5ULL) / 10ULL;
    return us - EPOCH_DIFFERENCE_USECS;
#else
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-member-init)
    timeval tv;
    if (gettimeofday(&tv, nullptr) < 0) return 0;
    return static_cast<uint64_t>(tv.tv_sec) * 1000000 + tv.tv_usec;
#endif
}

uint64_t V3Os::memUsageBytes() {
#if defined(_WIN32) || defined(__MINGW32__)
    const HANDLE process = GetCurrentProcess();
    PROCESS_MEMORY_COUNTERS pmc;
    if (GetProcessMemoryInfo(process, &pmc, sizeof(pmc))) {
        // The best we can do using simple Windows APIs is to get the size of the working set.
        return pmc.WorkingSetSize;
    }
    return 0;
#else
    // Highly unportable. Sorry
    const char* const statmFilename = "/proc/self/statm";
    FILE* fp = fopen(statmFilename, "r");
    if (!fp) return 0;
    uint64_t size, resident, share, text, lib, data, dt;  // All in pages
    const int items = fscanf(
        fp, "%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,
        &size, &resident, &share, &text, &lib, &data, &dt);
    fclose(fp);
    if (VL_UNCOVERABLE(7 != items)) return 0;
    return (text + data) * getpagesize();
#endif
}

void V3Os::u_sleep(int64_t usec) {
#if defined(_WIN32) || defined(__MINGW32__)
    std::this_thread::sleep_for(std::chrono::microseconds(usec));
#else
    // cppcheck-suppress obsoleteFunctionsusleep
    // Flawfinder: ignore
    ::usleep(usec);
#endif
}

//######################################################################
// METHODS (sub command)

int V3Os::system(const string& command) {
    UINFO(1, "Running system: " << command << endl);
    const int ret = ::system(command.c_str());
    if (VL_UNCOVERABLE(ret == -1)) {
        v3fatal("Failed to execute command:"  // LCOV_EXCL_LINE
                << command << " " << std::strerror(errno));
        return -1;  // LCOV_EXCL_LINE
    } else {
        UASSERT(WIFEXITED(ret), "system(" << command << ") returned unexpected value of " << ret);
        const int exit_code = WEXITSTATUS(ret);
        UINFO(1, command << " returned exit code of " << exit_code << std::endl);
        UASSERT(exit_code >= 0, "exit code must not be negative");
        return exit_code;
    }
}

//######################################################################
// METHODS (segfault handler)

#if defined(__linux__)
class ProcMapsParser final {

    int m_fd = -1;  // file descriptor
    std::array<char, 256> m_buf = {};  // chunk of data read from the file.
    const char* m_ccp = nullptr;  // pointer to current character.
    const char* m_endcp = nullptr;  // pointer to a character one past the end of data in m_buf.

private:
    // Moves m_ccp to the next character. Reads next chunk of data if needed.
    void advance() {
        if (m_ccp != m_endcp) {
            ++m_ccp;
        } else {
            const ssize_t len = read(m_fd, m_buf.data(), m_buf.size());
            const ssize_t buf_size = static_cast<ssize_t>(m_buf.size());
            if (len == buf_size) {
                m_ccp = &m_buf.front();
                m_endcp = m_ccp + (m_buf.size() - 1);
            } else if (len > 0 && len < buf_size) {
                m_buf[len] = '\0';
                m_ccp = m_buf.data();
                m_endcp = &m_buf[len];
            } else {
                m_buf[0] = '\0';
                m_ccp = m_buf.data();
                m_endcp = m_ccp;
            }
        }
    }

    // Moves m_cc to point at the first byte of the next line.
    void skip_line() {
        while (*m_ccp != '\n' && *m_ccp != '\0') { advance(); }
        if (*m_ccp == '\n') { advance(); }
    }

    uintptr_t parseHexNumber() {
        uintptr_t result = 0;

        for (;;) {
            if (*m_ccp >= '0' && *m_ccp <= '9') {
                result <<= 4;
                result |= *m_ccp - '0';
            } else if (*m_ccp >= 'a' && *m_ccp <= 'f') {
                result <<= 4;
                result |= *m_ccp - 'a' + 0xA;
            } else if (*m_ccp >= 'A' && *m_ccp <= 'F') {
                result <<= 4;
                result |= *m_ccp - 'A' + 0xA;
            } else {
                return result;
            }
            advance();
        }
    }

    bool open(const char* maps_path) {
        m_fd = ::open(maps_path, O_RDONLY | O_CLOEXEC);
        return m_fd >= 0;
    }

    void close() {
        if (m_fd >= 0) ::close(m_fd);
        m_fd = -1;
    }

public:
    ProcMapsParser() = default;
    ~ProcMapsParser() = default;
    ProcMapsParser(const ProcMapsParser&) = delete;
    ProcMapsParser(ProcMapsParser&&) = delete;
    ProcMapsParser& operator=(const ProcMapsParser&) = delete;
    ProcMapsParser& operator=(ProcMapsParser&&) = delete;

    struct MemoryRegion {
        std::uintptr_t begin;
        std::uintptr_t end;
    };

    // Parses "/proc/self/maps" and returns MemoryRegion containing addr_in_range.
    // Returns {0, 0} in case of failure.
    MemoryRegion find_address_range(std::uintptr_t addr_in_range) {
        if (!open("/proc/self/maps")) return {0, 0};

        // Syntax of every line in the maps file (simplified for our purposes):
        //   "{BEGIN_ADDR}-{END_ADDR} .*\n"
        // Where:
        //   {BEGIN_ADDR}: hexadecimal address of the region start.
        //   {END_ADDR}: hexadecimal address of the region end (exclusive).

        advance();  // get the first character
        while (*m_ccp != '\0') {
            const std::uintptr_t begin = parseHexNumber();
            advance();  // skip "-"
            const std::uintptr_t end = parseHexNumber();
            if (addr_in_range < end && begin <= addr_in_range) {
                close();
                return {begin, end};
            }
            skip_line();
        }
        close();
        return {0, 0};
    }
};

// Set when any thread started handling its own segfault. It prevents other threads which segfault
// at the same moment from running the handler code.
static std::atomic_flag segfaultHandlingInProgress = ATOMIC_FLAG_INIT;

// `someAddressOnThreadStackIsUndetermined` must be set when this variable is being changed.
static thread_local volatile std::uintptr_t someAddressOnThreadStack{0};

// Set when `someAddressOnThreadStack` is being assigned to.
static thread_local std::atomic_flag someAddressOnThreadStackIsUndetermined = ATOMIC_FLAG_INIT;

// Restores a default handler which will be called after returning from the current handler.
static void restoreDefaultSegfaultHandler() {
    struct sigaction sa = {};
    sa.sa_handler = SIG_DFL;
    sa.sa_flags = SA_ONSTACK;
    sigaction(SIGSEGV, &sa, nullptr);
}

extern "C" void v3SegfaultSignalHandler(int /*signo*/, siginfo_t* info, void* /*context*/) {
    if (segfaultHandlingInProgress.test_and_set(std::memory_order_acquire)) {
        // Other thread segfaulted too, and is already running this handler.
        // Wait for it to print relevant error and terminate the whole process.
        // Mutexes and similar things are not allowed in signal handlers, but sleep() is.
        // The sleep() doesn't prevent immediate termination, so it won't delay anything.
        for (;;) sleep(10);
    }

    if (someAddressOnThreadStackIsUndetermined.test_and_set(std::memory_order_acquire)
        || someAddressOnThreadStack == 0) {
        someAddressOnThreadStackIsUndetermined.clear(std::memory_order_release);
        // Finding the stack memory region is not possible without an address from the stack.
        return restoreDefaultSegfaultHandler();
    }
    // Parsing `maps` file and looking for a range containing known stack address is one of
    // probably only two methods to reliably find the stack memory region on Linux. The other one
    // is forking and using ptrace API to check rsp and rbp registers.
    // Custom parser is used here because scanf is not allowed in signal handlers.
    const auto stackRegion = ProcMapsParser().find_address_range(someAddressOnThreadStack);
    if (stackRegion.begin == 0) {
        // Failed to find stack region.
        return restoreDefaultSegfaultHandler();
    }
    const uintptr_t pageSize = sysconf(_SC_PAGESIZE);
    const uintptr_t faultAddr = reinterpret_cast<uintptr_t>(info->si_addr);

    // A short reminder how program's stack works:
    // - Grows down => overflow happens below the stack memory region.
    // - Each thread has its own stack.
    //   - Pthread's thread stack has constant size (by default equal to soft stack size limit[1]
    //     minus TLS data size)
    //   - Main thread's stack (its mapped memory region) grows dynamically until it reaches
    //     size equal to soft stack size limit[1].
    // - Stack allocations caused by local variables or calls to `alloca()` move stack pointer at
    //   most by one page size at a time (in a loop if needed). After each such move the memory
    //   page is "touched" (e.g. by writing its first byte). As a result, segfault caused by stack
    //   overflow can happen no farther than one page below the stack.
    //
    // [1]: See `ulimit -s` and `/etc/security/limits.conf`.

    // Stack on the beginning of address space probably never occurs. However, just in case
    // of some error in the stack region search code, make sure null is never considered to be the
    // address that caused stack overflow.
    const auto overflowAddrRangeBegin
        = (stackRegion.begin > pageSize) ? stackRegion.begin - pageSize : 1;
    const auto overflowAddrRangeEnd = stackRegion.begin;
    if (overflowAddrRangeBegin <= faultAddr && faultAddr < overflowAddrRangeEnd) {
        static const char msg[] = "\n"
                                  "Segmentation fault due to stack overflow.\n"
                                  "Try increasing stack size limit using `ulimit -s` command.\n"
                                  "\n";
        const auto result = write(STDERR_FILENO, msg, sizeof(msg) - 1);
        if (!result) {}  // Supress GCC's unused-result warning
    }

    return restoreDefaultSegfaultHandler();
}
#endif

void V3Os::setupThreadSegfaultSignalHandler() {
// Relies on /proc/self/maps; tested only on Linux.
#if defined(__linux__)
    // Segfault signal handler uses something between 300 and 400 bytes of the stack.
    // MINSIGSTKSZ may not be constant (it is a function call on some systems).
    // As a result we have to use dynamic memory below.
    static const std::size_t signalStackSize = (MINSIGSTKSZ < 1024) ? 1024 : MINSIGSTKSZ;
    // Stack used by all signal handlers in the current thread.
    static const thread_local std::unique_ptr<char[]> signalStackp{new char[signalStackSize]};

    stack_t altStack = {};
    altStack.ss_sp = signalStackp.get();
    altStack.ss_size = signalStackSize;
    sigaltstack(&altStack, nullptr);

    // `someAddressOnThreadStackIsUndetermined` is always unset here due to being thread_local.
    if (!someAddressOnThreadStackIsUndetermined.test_and_set(std::memory_order_acquire)) {
        // The address assigned to `someAddressOnThreadStack` doesn't really matter as long as it
        // is an address from the thread's stack. We know that local variables are on the stack of
        // the calling thread, so let's use `altStack` variable's address.
        someAddressOnThreadStack = reinterpret_cast<uintptr_t>(&altStack);
        someAddressOnThreadStackIsUndetermined.clear(std::memory_order_release);
    }

    // Indicates whether the process segfault handler has been set.
    static std::atomic_flag segfaultHandlerSet = ATOMIC_FLAG_INIT;

    if (!segfaultHandlerSet.test_and_set(std::memory_order_acquire)) {
        struct sigaction sa = {};
        sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
        sa.sa_sigaction = &v3SegfaultSignalHandler;
        if (sigaction(SIGSEGV, &sa, nullptr) < 0) {
            segfaultHandlerSet.clear(std::memory_order_release);
        }
    }
#endif
}
