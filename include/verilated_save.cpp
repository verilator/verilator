// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2001-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief C++ Tracing in VCD Format
///
//=============================================================================

#include "verilatedos.h"
#include "verilated.h"
#include "verilated_save.h"

#include <cerrno>
#include <fcntl.h>

// clang-format off
#if defined(_WIN32) && !defined(__MINGW32__) && !defined(__CYGWIN__)
# include <io.h>
#else
# include <unistd.h>
#endif

#ifndef O_LARGEFILE  // For example on WIN32
# define O_LARGEFILE 0
#endif
#ifndef O_NONBLOCK
# define O_NONBLOCK 0
#endif
#ifndef O_CLOEXEC
# define O_CLOEXEC 0
#endif
// clang-format on

// CONSTANTS
/// Value of first bytes of each file (must be multiple of 8 bytes)
static const char* const VLTSAVE_HEADER_STR = "verilatorsave01\n";
/// Value of last bytes of each file (must be multiple of 8 bytes)
static const char* const VLTSAVE_TRAILER_STR = "vltsaved";

//=============================================================================
//=============================================================================
//=============================================================================
// Searalization

bool VerilatedDeserialize::readDiffers(const void* __restrict datap,
                                       size_t size) VL_MT_UNSAFE_ONE {
    bufferCheck();
    const vluint8_t* __restrict dp = static_cast<const vluint8_t* __restrict>(datap);
    vluint8_t miss = 0;
    while (size--) miss |= (*dp++ ^ *m_cp++);
    return (miss != 0);
}

VerilatedDeserialize& VerilatedDeserialize::readAssert(const void* __restrict datap,
                                                       size_t size) VL_MT_UNSAFE_ONE {
    if (VL_UNLIKELY(readDiffers(datap, size))) {
        std::string fn = filename();
        std::string msg = "Can't deserialize save-restore file as was made from different model: "
                          + filename();
        VL_FATAL_MT(fn.c_str(), 0, "", msg.c_str());
        // Die before we close() as close would infinite loop
    }
    return *this;  // For function chaining
}

void VerilatedSerialize::header() VL_MT_UNSAFE_ONE {
    VerilatedSerialize& os = *this;  // So can cut and paste standard << code below
    assert((strlen(VLTSAVE_HEADER_STR) & 7) == 0);  // Keep aligned
    os.write(VLTSAVE_HEADER_STR, strlen(VLTSAVE_HEADER_STR));

    // Verilated doesn't do it itself, as if we're not using save/restore
    // it doesn't need to compile this stuff in
    os.write(Verilated::serialized1Ptr(), Verilated::serialized1Size());
    os.write(Verilated::serialized2Ptr(), Verilated::serialized2Size());
}

void VerilatedDeserialize::header() VL_MT_UNSAFE_ONE {
    VerilatedDeserialize& os = *this;  // So can cut and paste standard >> code below
    if (VL_UNLIKELY(os.readDiffers(VLTSAVE_HEADER_STR, strlen(VLTSAVE_HEADER_STR)))) {
        std::string fn = filename();
        std::string msg
            = std::string(
                  "Can't deserialize; file has wrong header signature, or file not found: ")
              + filename();
        VL_FATAL_MT(fn.c_str(), 0, "", msg.c_str());
        // Die before we close() as close would infinite loop
    }
    os.read(Verilated::serialized1Ptr(), Verilated::serialized1Size());
    os.read(Verilated::serialized2Ptr(), Verilated::serialized2Size());
}

void VerilatedSerialize::trailer() VL_MT_UNSAFE_ONE {
    VerilatedSerialize& os = *this;  // So can cut and paste standard << code below
    assert((strlen(VLTSAVE_TRAILER_STR) & 7) == 0);  // Keep aligned
    os.write(VLTSAVE_TRAILER_STR, strlen(VLTSAVE_TRAILER_STR));
}

void VerilatedDeserialize::trailer() VL_MT_UNSAFE_ONE {
    VerilatedDeserialize& os = *this;  // So can cut and paste standard >> code below
    if (VL_UNLIKELY(os.readDiffers(VLTSAVE_TRAILER_STR, strlen(VLTSAVE_TRAILER_STR)))) {
        std::string fn = filename();
        std::string msg = std::string("Can't deserialize; file has wrong end-of-file signature: ")
                          + filename();
        VL_FATAL_MT(fn.c_str(), 0, "", msg.c_str());
        // Die before we close() as close would infinite loop
    }
}

//=============================================================================
//=============================================================================
//=============================================================================
// Opening/Closing

void VerilatedSave::open(const char* filenamep) VL_MT_UNSAFE_ONE {
    m_assertOne.check();
    if (isOpen()) return;
    VL_DEBUG_IF(VL_DBG_MSGF("- save: opening save file %s\n", filenamep););

    if (VL_UNCOVERABLE(filenamep[0] == '|')) {
        assert(0);  // LCOV_EXCL_LINE // Not supported yet.
    } else {
        // cppcheck-suppress duplicateExpression
        m_fd = ::open(filenamep,
                      O_CREAT | O_WRONLY | O_TRUNC | O_LARGEFILE | O_NONBLOCK | O_CLOEXEC, 0666);
        if (VL_UNLIKELY(m_fd < 0)) {
            // User code can check isOpen()
            m_isOpen = false;
            return;
        }
    }
    m_isOpen = true;
    m_filename = filenamep;
    m_cp = m_bufp;
    header();
}

void VerilatedRestore::open(const char* filenamep) VL_MT_UNSAFE_ONE {
    m_assertOne.check();
    if (isOpen()) return;
    VL_DEBUG_IF(VL_DBG_MSGF("- restore: opening restore file %s\n", filenamep););

    if (VL_UNCOVERABLE(filenamep[0] == '|')) {
        assert(0);  // LCOV_EXCL_LINE // Not supported yet.
    } else {
        // cppcheck-suppress duplicateExpression
        m_fd = ::open(filenamep, O_CREAT | O_RDONLY | O_LARGEFILE | O_CLOEXEC, 0666);
        if (VL_UNLIKELY(m_fd < 0)) {
            // User code can check isOpen()
            m_isOpen = false;
            return;
        }
    }
    m_isOpen = true;
    m_filename = filenamep;
    m_cp = m_bufp;
    m_endp = m_bufp;
    header();
}

void VerilatedSave::close() VL_MT_UNSAFE_ONE {
    if (!isOpen()) return;
    trailer();
    flush();
    m_isOpen = false;
    ::close(m_fd);  // May get error, just ignore it
}

void VerilatedRestore::close() VL_MT_UNSAFE_ONE {
    if (!isOpen()) return;
    trailer();
    flush();
    m_isOpen = false;
    ::close(m_fd);  // May get error, just ignore it
}

//=============================================================================
// Buffer management

void VerilatedSave::flush() VL_MT_UNSAFE_ONE {
    m_assertOne.check();
    if (VL_UNLIKELY(!isOpen())) return;
    vluint8_t* wp = m_bufp;
    while (true) {
        ssize_t remaining = (m_cp - wp);
        if (remaining == 0) break;
        errno = 0;
        ssize_t got = ::write(m_fd, wp, remaining);
        if (got > 0) {
            wp += got;
        } else if (VL_UNCOVERABLE(got < 0)) {
            if (VL_UNCOVERABLE(errno != EAGAIN && errno != EINTR)) {
                // LCOV_EXCL_START
                // write failed, presume error (perhaps out of disk space)
                std::string msg = std::string(__FUNCTION__) + ": " + strerror(errno);
                VL_FATAL_MT("", 0, "", msg.c_str());
                close();
                break;
                // LCOV_EXCL_STOP
            }
        }
    }
    m_cp = m_bufp;  // Reset buffer
}

void VerilatedRestore::fill() VL_MT_UNSAFE_ONE {
    m_assertOne.check();
    if (VL_UNLIKELY(!isOpen())) return;
    // Move remaining characters down to start of buffer.  (No memcpy, overlaps allowed)
    vluint8_t* rp = m_bufp;
    for (vluint8_t* sp = m_cp; sp < m_endp; *rp++ = *sp++) {}  // Overlaps
    m_endp = m_bufp + (m_endp - m_cp);
    m_cp = m_bufp;  // Reset buffer
    // Read into buffer starting at m_endp
    while (true) {
        ssize_t remaining = (m_bufp + bufferSize() - m_endp);
        if (remaining == 0) break;
        errno = 0;
        ssize_t got = ::read(m_fd, m_endp, remaining);
        if (got > 0) {
            m_endp += got;
        } else if (VL_UNCOVERABLE(got < 0)) {
            if (VL_UNCOVERABLE(errno != EAGAIN && errno != EINTR)) {
                // LCOV_EXCL_START
                // write failed, presume error (perhaps out of disk space)
                std::string msg = std::string(__FUNCTION__) + ": " + strerror(errno);
                VL_FATAL_MT("", 0, "", msg.c_str());
                close();
                break;
                // LCOV_EXCL_STOP
            }
        } else {  // got==0, EOF
            // Fill buffer from here to end with NULLs so reader's don't
            // need to check eof each character.
            while (m_endp < m_bufp + bufferSize()) *m_endp++ = '\0';
            break;
        }
    }
}

//=============================================================================
// Serialization of types
