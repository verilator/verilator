// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2012-2015 by Wilson Snyder.  This program is free software;
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
/// \brief Save-restore serialization of verilated modules
///
//=============================================================================

#ifndef _VERILATED_SAVE_C_H_
#define _VERILATED_SAVE_C_H_ 1

#include "verilatedos.h"

#include <string>
using namespace std;

//=============================================================================
// VerilatedSerialBase - internal base class for common code between VerilatedSerialize and VerilatedDeserialize

class VerilatedSerialBase {
protected:
    // MEMBERS
    // For speed, keep m_cp as the first member of this structure
    vluint8_t*		m_cp;		///< Current pointer into m_bufp buffer
    vluint8_t*		m_bufp;		///< Output buffer
    bool 		m_isOpen;	///< True indicates open file/stream
    string		m_filename;

    inline static size_t bufferSize() { return 256*1024; }  // See below for slack calculation
    inline static size_t bufferInsertSize() { return 16*1024; }

    // CREATORS
    VerilatedSerialBase() {
	m_isOpen = false;
	m_bufp = new vluint8_t [bufferSize()];
	m_cp = m_bufp;
    }
public:
    // CREATORS
    virtual ~VerilatedSerialBase() {
	close();
	if (m_bufp) { delete m_bufp; m_bufp=NULL; }
    }
    // METHODS
    bool isOpen() const { return m_isOpen; }
    string filename() const { return m_filename; }
    virtual void close() { flush(); }
    virtual void flush() {}
};

//=============================================================================
// VerilatedSerialize - convert structures to a stream representation

class VerilatedSerialize : public VerilatedSerialBase {
protected:
    virtual void close() { flush(); }
    virtual void flush() {}
    void header();
    void trailer();
public:
    // CREATORS
    VerilatedSerialize() {}
    virtual ~VerilatedSerialize() { close(); }
    // METHODS
    VerilatedSerialize& bufferCheck() {
	// Flush the write buffer if there's not enough space left for new information
	// We only call this once per vector, so we need enough slop for a very wide "b###" line
	if (VL_UNLIKELY(m_cp > (m_bufp+(bufferSize()-bufferInsertSize())))) {
	    flush();
	}
	return *this;  // For function chaining
    }
    inline VerilatedSerialize& write (const void* __restrict datap, size_t size) {
	const vluint8_t* __restrict dp = (const vluint8_t* __restrict)datap;
	while (size) {
	    bufferCheck();
	    size_t blk = size;  if (blk>bufferInsertSize()) blk = bufferInsertSize();
	    const vluint8_t* __restrict maxp = dp + blk;
	    while (dp < maxp) *m_cp++ = *dp++;
	    size -= blk;
	}
	return *this;  // For function chaining
    }
};

//=============================================================================
// VerilatedDeserial - load structures from a stream representation

class VerilatedDeserialize : public VerilatedSerialBase {
protected:
    vluint8_t*		m_endp;		///< Last valid byte in m_bufp buffer
    virtual void fill() = 0;
    void header();
    void trailer();
public:
    // CREATORS
    VerilatedDeserialize() { m_endp = NULL; }
    virtual ~VerilatedDeserialize() { close(); }
    // METHODS
    inline VerilatedDeserialize& read (void* __restrict datap, size_t size) {
	vluint8_t* __restrict dp = (vluint8_t* __restrict)datap;
	while (size) {
	    bufferCheck();
	    size_t blk = size;  if (blk>bufferInsertSize()) blk = bufferInsertSize();
	    const vluint8_t* __restrict maxp = dp + blk;
	    while (dp < maxp) *dp++ = *m_cp++;
	    size -= blk;
	}
	return *this;  // For function chaining
    }
    // Read a datum and compare with expected value
    bool readDiffers (const void* __restrict datap, size_t size);
    VerilatedDeserialize& readAssert (const void* __restrict datap, size_t size);
    VerilatedDeserialize& readAssert (vluint64_t data) { return readAssert(&data, sizeof(data)); }
    VerilatedDeserialize& bufferCheck() {
	// Flush the write buffer if there's not enough space left for new information
	// We only call this once per vector, so we need enough slop for a very wide "b###" line
	if (VL_UNLIKELY((m_cp+bufferInsertSize()) > m_endp)) {
	    fill();
	}
	return *this;  // For function chaining
    }
};

//=============================================================================
// VerilatedSave - serialize to a file

class VerilatedSave : public VerilatedSerialize {
private:
    int			m_fd;		///< File descriptor we're writing to

public:
    // CREATORS
    VerilatedSave() { m_fd=-1; }
    virtual ~VerilatedSave() { close(); }
    // METHODS
    void open(const char* filenamep);	///< Open the file; call isOpen() to see if errors
    void open(const string& filename) { open(filename.c_str()); }
    virtual void close();
    virtual void flush();
};

//=============================================================================
// VerilatedRestore - deserialize from a file

class VerilatedRestore : public VerilatedDeserialize {
private:
    int			m_fd;		///< File descriptor we're writing to

public:
    // CREATORS
    VerilatedRestore() { m_fd=-1; }
    virtual ~VerilatedRestore() { close(); }

    // METHODS
    void open(const char* filenamep);	///< Open the file; call isOpen() to see if errors
    void open(const string& filename) { open(filename.c_str()); }
    virtual void close();
    virtual void flush() {}
    virtual void fill();
};

//=============================================================================

inline VerilatedSerialize&   operator<<(VerilatedSerialize& os,   vluint64_t& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, vluint64_t& rhs){
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize&   operator<<(VerilatedSerialize& os,   vluint32_t& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, vluint32_t& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize&   operator<<(VerilatedSerialize& os,   vluint16_t& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, vluint16_t& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize&   operator<<(VerilatedSerialize& os,   vluint8_t& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, vluint8_t& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize&   operator<<(VerilatedSerialize& os,   bool& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, bool& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize&   operator<<(VerilatedSerialize& os,   double& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, double& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize&   operator<<(VerilatedSerialize& os,   float& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, float& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize&   operator<<(VerilatedSerialize& os,   string& rhs) {
    vluint32_t len=rhs.length();
    os<<len;
    return os.write(rhs.data(), len);
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, string& rhs) {
    vluint32_t len;
    os>>len;
    rhs.resize(len);
    return os.read((void*)rhs.data(), len);
}

#endif // guard
