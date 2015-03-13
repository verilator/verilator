// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2001-2015 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
//
// This is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
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

#include <fcntl.h>
#include <cerrno>

#if defined(_WIN32) && !defined(__MINGW32__) && !defined(__CYGWIN__)
# include <io.h>
#else
# include <unistd.h>
#endif

#ifndef O_LARGEFILE // For example on WIN32
# define O_LARGEFILE 0
#endif
#ifndef O_NONBLOCK
# define O_NONBLOCK 0
#endif

// CONSTANTS
static const char* VLTSAVE_HEADER_STR = "verilatorsave01\n";	///< Value of first bytes of each file
static const char* VLTSAVE_TRAILER_STR = "vltsaved";	///< Value of last bytes of each file

//=============================================================================
//=============================================================================
//=============================================================================
// Searalization

bool VerilatedDeserialize::readDiffers (const void* __restrict datap, size_t size) {
    bufferCheck();
    const vluint8_t* __restrict dp = (const vluint8_t* __restrict)datap;
    vluint8_t miss = 0;
    while (size--) {
	miss |= (*dp++ ^ *m_cp++);
    }
    return (miss!=0);
}

VerilatedDeserialize& VerilatedDeserialize::readAssert (const void* __restrict datap, size_t size) {
    if (VL_UNLIKELY(readDiffers(datap,size))) {
	string fn = filename();
	string msg = (string)"Can't deserialize save-restore file as was made from different model";
	vl_fatal(fn.c_str(), 0, "", msg.c_str());
	close();
    }
    return *this;  // For function chaining
}

void VerilatedSerialize::header() {
    VerilatedSerialize& os = *this;  // So can cut and paste standard << code below
    assert((strlen(VLTSAVE_HEADER_STR) & 7) == 0);  // Keep aligned
    os.write(VLTSAVE_HEADER_STR, strlen(VLTSAVE_HEADER_STR));

    // Verilated doesn't do it itself, as if we're not using save/restore
    // it doesn't need to compile this stuff in
    os.write(Verilated::serializedPtr(), Verilated::serializedSize());
}

void VerilatedDeserialize::header() {
    VerilatedDeserialize& os = *this;  // So can cut and paste standard >> code below
    if (VL_UNLIKELY(os.readDiffers(VLTSAVE_HEADER_STR, strlen(VLTSAVE_HEADER_STR)))) {
	string fn = filename();
	string msg = (string)"Can't deserialize; file has wrong header signature";
	vl_fatal(fn.c_str(), 0, "", msg.c_str());
	close();
    }
    os.read(Verilated::serializedPtr(), Verilated::serializedSize());
}

void VerilatedSerialize::trailer() {
    VerilatedSerialize& os = *this;  // So can cut and paste standard << code below
    assert((strlen(VLTSAVE_TRAILER_STR) & 7) == 0);  // Keep aligned
    os.write(VLTSAVE_TRAILER_STR, strlen(VLTSAVE_TRAILER_STR));
}

void VerilatedDeserialize::trailer() {
    VerilatedDeserialize& os = *this;  // So can cut and paste standard >> code below
    if (VL_UNLIKELY(os.readDiffers(VLTSAVE_TRAILER_STR, strlen(VLTSAVE_TRAILER_STR)))) {
	string fn = filename();
	string msg = (string)"Can't deserialize; file has wrong end-of-file signature";
	vl_fatal(fn.c_str(), 0, "", msg.c_str());
	close();
    }
}

//=============================================================================
//=============================================================================
//=============================================================================
// Opening/Closing

void VerilatedSave::open (const char* filenamep) {
    if (isOpen()) return;
    VL_DEBUG_IF(VL_PRINTF("-vltSave: opening save file %s\n",filenamep););

    if (filenamep[0]=='|') {
	assert(0);	// Not supported yet.
    } else {
	// cppcheck-suppress duplicateExpression
	m_fd = ::open (filenamep, O_CREAT|O_WRONLY|O_TRUNC|O_LARGEFILE|O_NONBLOCK
		       , 0666);
	if (m_fd<0) {
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

void VerilatedRestore::open (const char* filenamep) {
    if (isOpen()) return;
    VL_DEBUG_IF(VL_PRINTF("-vltRestore: opening restore file %s\n",filenamep););

    if (filenamep[0]=='|') {
	assert(0);	// Not supported yet.
    } else {
	// cppcheck-suppress duplicateExpression
	m_fd = ::open (filenamep, O_CREAT|O_RDONLY|O_LARGEFILE
		       , 0666);
	if (m_fd<0) {
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

void VerilatedSave::close () {
    if (!isOpen()) return;
    trailer();
    flush();
    m_isOpen = false;
    ::close(m_fd);  // May get error, just ignore it
}

void VerilatedRestore::close () {
    if (!isOpen()) return;
    trailer();
    flush();
    m_isOpen = false;
    ::close(m_fd);  // May get error, just ignore it
}

//=============================================================================
// Buffer management

void VerilatedSave::flush() {
    if (VL_UNLIKELY(!isOpen())) return;
    vluint8_t* wp = m_bufp;
    while (1) {
	ssize_t remaining = (m_cp - wp);
	if (remaining==0) break;
	errno = 0;
	ssize_t got = ::write (m_fd, wp, remaining);
	if (got>0) {
	    wp += got;
	} else if (got < 0) {
	    if (errno != EAGAIN && errno != EINTR) {
		// write failed, presume error (perhaps out of disk space)
		string msg = string(__FUNCTION__)+": "+strerror(errno);
		vl_fatal("",0,"",msg.c_str());
		close();
		break;
	    }
	}
    }
    m_cp = m_bufp; // Reset buffer
}

void VerilatedRestore::fill() {
    if (VL_UNLIKELY(!isOpen())) return;
    // Move remaining characters down to start of buffer.  (No memcpy, overlaps allowed)
    vluint8_t* rp = m_bufp;
    for (vluint8_t* sp=m_cp; rp < m_endp;) *rp++ = *sp++;  // Overlaps
    m_endp = m_bufp + (m_endp - m_cp);
    m_cp = m_bufp; // Reset buffer
    // Read into buffer starting at m_endp 
    while (1) {
	ssize_t remaining = (m_bufp+bufferSize() - m_endp);
	if (remaining==0) break;
	errno = 0;
	ssize_t got = ::read (m_fd, m_endp, remaining);
	if (got>0) {
	    m_endp += got;
	} else if (got < 0) {
	    if (errno != EAGAIN && errno != EINTR) {
		// write failed, presume error (perhaps out of disk space)
		string msg = string(__FUNCTION__)+": "+strerror(errno);
		vl_fatal("",0,"",msg.c_str());
		close();
		break;
	    }
	} else { // got==0, EOF
	    // Fill buffer from here to end with NULLs so reader's don't need to check eof each character.
	    while (m_endp < m_bufp+bufferSize()) *m_endp++ = '\0';
	    break;
	}
    }
}

//=============================================================================
// Serialization of types


