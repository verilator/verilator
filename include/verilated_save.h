// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2000-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
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
#include "verilated_heavy.h"

#include <string>

//=============================================================================
// VerilatedSerialize - convert structures to a stream representation
// This class is not thread safe, it must be called by a single thread

class VerilatedSerialize {
protected:
    // MEMBERS
    // For speed, keep m_cp as the first member of this structure
    vluint8_t* m_cp;  ///< Current pointer into m_bufp buffer
    vluint8_t* m_bufp;  ///< Output buffer
    bool m_isOpen;  ///< True indicates open file/stream
    std::string m_filename;  ///< Filename, for error messages
    VerilatedAssertOneThread m_assertOne;  ///< Assert only called from single thread

    inline static size_t bufferSize() { return 256 * 1024; }  // See below for slack calculation
    inline static size_t bufferInsertSize() { return 16 * 1024; }

    void header() VL_MT_UNSAFE_ONE;
    void trailer() VL_MT_UNSAFE_ONE;

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedSerialize);
public:
    VerilatedSerialize() {
        m_isOpen = false;
        m_bufp = new vluint8_t[bufferSize()];
        m_cp = m_bufp;
    }
    virtual ~VerilatedSerialize() {
        close();
        if (m_bufp) { delete m_bufp; m_bufp=NULL; }
    }
    // METHODS
    bool isOpen() const { return m_isOpen; }
    std::string filename() const { return m_filename; }
    virtual void close() VL_MT_UNSAFE_ONE { flush(); }
    virtual void flush() VL_MT_UNSAFE_ONE {}
    inline VerilatedSerialize& write(const void* __restrict datap, size_t size) VL_MT_UNSAFE_ONE {
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
private:
    VerilatedSerialize& bufferCheck() VL_MT_UNSAFE_ONE {
        // Flush the write buffer if there's not enough space left for new information
        // We only call this once per vector, so we need enough slop for a very wide "b###" line
        if (VL_UNLIKELY(m_cp > (m_bufp+(bufferSize()-bufferInsertSize())))) {
            flush();
        }
        return *this;  // For function chaining
    }
};

//=============================================================================
// VerilatedDeserial - load structures from a stream representation
// This class is not thread safe, it must be called by a single thread

class VerilatedDeserialize {
protected:
    // MEMBERS
    // For speed, keep m_cp as the first member of this structure
    vluint8_t* m_cp;  ///< Current pointer into m_bufp buffer
    vluint8_t* m_bufp;  ///< Output buffer
    vluint8_t* m_endp;  ///< Last valid byte in m_bufp buffer
    bool m_isOpen;  ///< True indicates open file/stream
    std::string m_filename;  ///< Filename, for error messages
    VerilatedAssertOneThread m_assertOne;  ///< Assert only called from single thread

    inline static size_t bufferSize() { return 256 * 1024; }  // See below for slack calculation
    inline static size_t bufferInsertSize() { return 16 * 1024; }

    virtual void fill() = 0;
    void header() VL_MT_UNSAFE_ONE;
    void trailer() VL_MT_UNSAFE_ONE;

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedDeserialize);
public:
    VerilatedDeserialize() {
        m_isOpen = false;
        m_bufp = new vluint8_t[bufferSize()];
        m_cp = m_bufp;
        m_endp = NULL;
    }
    virtual ~VerilatedDeserialize() {
        close();
        if (m_bufp) { delete m_bufp; m_bufp=NULL; }
    }
    // METHODS
    bool isOpen() const { return m_isOpen; }
    std::string filename() const { return m_filename; }
    virtual void close() VL_MT_UNSAFE_ONE { flush(); }
    virtual void flush() VL_MT_UNSAFE_ONE {}
    inline VerilatedDeserialize& read(void* __restrict datap, size_t size) VL_MT_UNSAFE_ONE {
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
    VerilatedDeserialize& readAssert(const void* __restrict datap, size_t size) VL_MT_UNSAFE_ONE;
    VerilatedDeserialize& readAssert(vluint64_t data) VL_MT_UNSAFE_ONE {
        return readAssert(&data, sizeof(data)); }
private:
    bool readDiffers(const void* __restrict datap, size_t size) VL_MT_UNSAFE_ONE;
    VerilatedDeserialize& bufferCheck() VL_MT_UNSAFE_ONE {
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
// This class is not thread safe, it must be called by a single thread

class VerilatedSave : public VerilatedSerialize {
private:
    int m_fd;  ///< File descriptor we're writing to

public:
    // CONSTRUCTORS
    VerilatedSave() { m_fd = -1; }
    virtual ~VerilatedSave() VL_OVERRIDE { close(); }
    // METHODS
    void open(const char* filenamep) VL_MT_UNSAFE_ONE;  ///< Open the file; call isOpen() to see if errors
    void open(const std::string& filename) VL_MT_UNSAFE_ONE { open(filename.c_str()); }
    virtual void close() VL_OVERRIDE VL_MT_UNSAFE_ONE;
    virtual void flush() VL_OVERRIDE VL_MT_UNSAFE_ONE;
};

//=============================================================================
// VerilatedRestore - deserialize from a file
// This class is not thread safe, it must be called by a single thread

class VerilatedRestore : public VerilatedDeserialize {
private:
    int m_fd;  ///< File descriptor we're writing to

public:
    // CONSTRUCTORS
    VerilatedRestore() { m_fd = -1; }
    virtual ~VerilatedRestore() VL_OVERRIDE { close(); }

    // METHODS
    void open(const char* filenamep) VL_MT_UNSAFE_ONE;  ///< Open the file; call isOpen() to see if errors
    void open(const std::string& filename) VL_MT_UNSAFE_ONE { open(filename.c_str()); }
    virtual void close() VL_OVERRIDE VL_MT_UNSAFE_ONE;
    virtual void flush() VL_OVERRIDE VL_MT_UNSAFE_ONE {}
    virtual void fill() VL_OVERRIDE VL_MT_UNSAFE_ONE;
};

//=============================================================================

inline VerilatedSerialize& operator<<(VerilatedSerialize& os, vluint64_t& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, vluint64_t& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize& operator<<(VerilatedSerialize& os, vluint32_t& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, vluint32_t& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize& operator<<(VerilatedSerialize& os, vluint16_t& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, vluint16_t& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize& operator<<(VerilatedSerialize& os, vluint8_t& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, vluint8_t& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize& operator<<(VerilatedSerialize& os, bool& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, bool& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize& operator<<(VerilatedSerialize& os, double& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, double& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize& operator<<(VerilatedSerialize& os, float& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, float& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize& operator<<(VerilatedSerialize& os, std::string& rhs) {
    vluint32_t len = rhs.length();
    os << len;
    return os.write(rhs.data(), len);
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, std::string& rhs) {
    vluint32_t len = 0;
    os >> len;
    rhs.resize(len);
    return os.read((void*)rhs.data(), len);
}
template <class T_Key, class T_Value>
VerilatedSerialize& operator<<(VerilatedSerialize& os, VlAssocArray<T_Key, T_Value>& rhs) {
    os << rhs.atDefault();
    vluint32_t len = rhs.size();
    os << len;
    for (typename VlAssocArray<T_Key, T_Value>::const_iterator it = rhs.begin();
         it != rhs.end(); ++it) {
        T_Key index = it->first;  // Copy to get around const_iterator
        T_Value value = it->second;
        os << index << value;
    }
    return os;
}
template <class T_Key, class T_Value>
VerilatedDeserialize& operator>>(VerilatedDeserialize& os, VlAssocArray<T_Key, T_Value>& rhs) {
    os >> rhs.atDefault();
    vluint32_t len = 0;
    os >> len;
    rhs.clear();
    for (vluint32_t i = 0; i < len; ++i) {
        T_Key index;
        T_Value value;
        os >> index;
        os >> value;
        rhs.at(index) = value;
    }
    return os;
}

#endif  // Guard
