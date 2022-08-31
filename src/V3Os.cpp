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
#include "V3String.h"
#include "V3Os.h"

#include <cerrno>
#include <climits>  // PATH_MAX (especially on FreeBSD)
#include <cstdarg>
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
                << command << " " << strerror(errno));
        return -1;  // LCOV_EXCL_LINE
    } else {
        UASSERT(WIFEXITED(ret), "system(" << command << ") returned unexpected value of " << ret);
        const int exit_code = WEXITSTATUS(ret);
        UINFO(1, command << " returned exit code of " << exit_code << std::endl);
        UASSERT(exit_code >= 0, "exit code must not be negative");
        return exit_code;
    }
}
