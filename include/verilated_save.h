// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// Copyright 2000-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated save-restore serialization header
///
/// This must be included in user wrapper code that wants to use
/// save/restore.
///
//=============================================================================

#ifndef VERILATOR_VERILATED_SAVE_C_H_
#define VERILATOR_VERILATED_SAVE_C_H_

#include "verilatedos.h"

#include "verilated.h"

#include <string>

//=============================================================================
// VerilatedSerialize
/// Class for writing serialization of structures to a stream representation.
///
/// User wrapper code will more typically use VerilatedSave which uses this
/// as a subclass to write a file.
///
/// This class is not thread safe, it must be called by a single thread

class VerilatedSerialize VL_NOT_FINAL {
protected:
    // MEMBERS
    // For speed, keep m_cp as the first member of this structure
    uint8_t* m_cp;  // Current pointer into m_bufp buffer
    uint8_t* m_bufp;  // Output buffer
    bool m_isOpen = false;  // True indicates open file/stream
    std::string m_filename;  // Filename, for error messages
    VerilatedAssertOneThread m_assertOne;  // Assert only called from single thread

    static constexpr size_t bufferSize() { return 256 * 1024; }  // See below for slack calculation
    static constexpr size_t bufferInsertSize() { return 16 * 1024; }

    void header() VL_MT_UNSAFE_ONE;
    void trailer() VL_MT_UNSAFE_ONE;

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedSerialize);

public:
    /// Construct
    VerilatedSerialize() {
        m_bufp = new uint8_t[bufferSize()];
        m_cp = m_bufp;
    }
    /// Flish, close, and destruct
    virtual ~VerilatedSerialize() {
        close();
        if (m_bufp) VL_DO_CLEAR(delete[] m_bufp, m_bufp = nullptr);
    }
    // METHODS
    /// Return true if file is open
    bool isOpen() const { return m_isOpen; }
    /// Return current filename
    std::string filename() const { return m_filename; }
    /// Close the stream
    virtual void close() VL_MT_UNSAFE_ONE { flush(); }
    /// Flush pending data to stream
    virtual void flush() VL_MT_UNSAFE_ONE {}
    /// Write data to stream
    VerilatedSerialize& write(const void* __restrict datap, size_t size) VL_MT_UNSAFE_ONE {
        const uint8_t* __restrict dp = static_cast<const uint8_t* __restrict>(datap);
        while (size) {
            bufferCheck();
            size_t blk = size;
            if (blk > bufferInsertSize()) blk = bufferInsertSize();
            const uint8_t* __restrict maxp = dp + blk;
            for (; dp < maxp; *m_cp++ = *dp++) {}
            size -= blk;
        }
        return *this;  // For function chaining
    }

private:
    VerilatedSerialize& bufferCheck() VL_MT_UNSAFE_ONE {
        // Flush the write buffer if there's not enough space left for new information
        // We only call this once per vector, so we need enough slop for a very wide "b###" line
        if (VL_UNLIKELY(m_cp > (m_bufp + (bufferSize() - bufferInsertSize())))) flush();
        return *this;  // For function chaining
    }
};

//=============================================================================
// VerilatedDeserialize
/// Class for loading structures from a stream representation.
///
/// User wrapper code will more typically use VerilatedRestore which uses
/// this as a subclass to a read from a file.
///
/// This class is not thread safe, it must be called by a single thread

class VerilatedDeserialize VL_NOT_FINAL {
protected:
    // MEMBERS
    // For speed, keep m_cp as the first member of this structure
    uint8_t* m_cp;  // Current pointer into m_bufp buffer
    uint8_t* m_bufp;  // Output buffer
    uint8_t* m_endp = nullptr;  // Last valid byte in m_bufp buffer
    bool m_isOpen = false;  // True indicates open file/stream
    std::string m_filename;  // Filename, for error messages
    VerilatedAssertOneThread m_assertOne;  // Assert only called from single thread

    static constexpr size_t bufferSize() { return 256 * 1024; }  // See below for slack calculation
    static constexpr size_t bufferInsertSize() { return 16 * 1024; }

    virtual void fill() = 0;
    void header() VL_MT_UNSAFE_ONE;
    void trailer() VL_MT_UNSAFE_ONE;

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedDeserialize);

public:
    /// Construct
    VerilatedDeserialize() {
        m_bufp = new uint8_t[bufferSize()];
        m_cp = m_bufp;
    }
    /// Destruct
    virtual ~VerilatedDeserialize() {
        close();
        if (m_bufp) VL_DO_CLEAR(delete[] m_bufp, m_bufp = nullptr);
    }
    // METHODS
    /// Return true if file is open
    bool isOpen() const { return m_isOpen; }
    /// Return current filename
    std::string filename() const { return m_filename; }
    /// Close the stream
    virtual void close() VL_MT_UNSAFE_ONE { flush(); }
    /// Flush pending data to stream
    virtual void flush() VL_MT_UNSAFE_ONE {}
    /// Read data from stream
    VerilatedDeserialize& read(void* __restrict datap, size_t size) VL_MT_UNSAFE_ONE {
        uint8_t* __restrict dp = static_cast<uint8_t* __restrict>(datap);
        while (size) {
            bufferCheck();
            size_t blk = size;
            if (blk > bufferInsertSize()) blk = bufferInsertSize();
            const uint8_t* __restrict maxp = dp + blk;
            for (; dp < maxp; *dp++ = *m_cp++) {}
            size -= blk;
        }
        return *this;  // For function chaining
    }

    // Internal use:
    // Read a datum and compare with expected value
    VerilatedDeserialize& readAssert(const void* __restrict datap, size_t size) VL_MT_UNSAFE_ONE;
    VerilatedDeserialize& readAssert(uint64_t data) VL_MT_UNSAFE_ONE {
        return readAssert(&data, sizeof(data));
    }

private:
    bool readDiffers(const void* __restrict datap, size_t size) VL_MT_UNSAFE_ONE;
    VerilatedDeserialize& bufferCheck() VL_MT_UNSAFE_ONE {
        // Flush the write buffer if there's not enough space left for new information
        // We only call this once per vector, so we need enough slop for a very wide "b###" line
        if (VL_UNLIKELY((m_cp + bufferInsertSize()) > m_endp)) fill();
        return *this;  // For function chaining
    }
};

//=============================================================================
// VerilatedSave
/// Stream-like object that serializes Verilated model to a file.
///
/// This class is not thread safe, it must be called by a single thread

class VerilatedSave final : public VerilatedSerialize {
private:
    int m_fd = -1;  // File descriptor we're writing to

public:
    // CONSTRUCTORS
    /// Construct new object
    VerilatedSave() = default;
    /// Flush, close and destruct
    ~VerilatedSave() override { close(); }
    // METHODS
    /// Open the file; call isOpen() to see if errors
    void open(const char* filenamep) VL_MT_UNSAFE_ONE;
    /// Open the file; call isOpen() to see if errors
    void open(const std::string& filename) VL_MT_UNSAFE_ONE { open(filename.c_str()); }
    /// Flush and close the file
    void close() override VL_MT_UNSAFE_ONE;
    /// Flush data to file
    void flush() override VL_MT_UNSAFE_ONE;
};

//=============================================================================
// VerilatedRestore
/// Stream-like object that serializes Verilated model from a file.
///
/// This class is not thread safe, it must be called by a single thread

class VerilatedRestore final : public VerilatedDeserialize {
private:
    int m_fd = -1;  // File descriptor we're writing to

public:
    // CONSTRUCTORS
    /// Construct new object
    VerilatedRestore() = default;
    /// Flush, close and destruct
    ~VerilatedRestore() override { close(); }

    // METHODS
    /// Open the file; call isOpen() to see if errors
    void open(const char* filenamep) VL_MT_UNSAFE_ONE;
    /// Open the file; call isOpen() to see if errors
    void open(const std::string& filename) VL_MT_UNSAFE_ONE { open(filename.c_str()); }
    /// Close the file
    void close() override VL_MT_UNSAFE_ONE;
    void flush() override VL_MT_UNSAFE_ONE {}
    void fill() override VL_MT_UNSAFE_ONE;
};

//=============================================================================

inline VerilatedSerialize& operator<<(VerilatedSerialize& os, const uint64_t& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, uint64_t& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize& operator<<(VerilatedSerialize& os, const uint32_t& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, uint32_t& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize& operator<<(VerilatedSerialize& os, const uint16_t& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, uint16_t& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize& operator<<(VerilatedSerialize& os, const uint8_t& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, uint8_t& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize& operator<<(VerilatedSerialize& os, const bool& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, bool& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize& operator<<(VerilatedSerialize& os, const double& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, double& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize& operator<<(VerilatedSerialize& os, const float& rhs) {
    return os.write(&rhs, sizeof(rhs));
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, float& rhs) {
    return os.read(&rhs, sizeof(rhs));
}
inline VerilatedSerialize& operator<<(VerilatedSerialize& os, const std::string& rhs) {
    const uint32_t len = rhs.length();
    os << len;
    return os.write(rhs.data(), len);
}
inline VerilatedDeserialize& operator>>(VerilatedDeserialize& os, std::string& rhs) {
    uint32_t len = 0;
    os >> len;
    rhs.resize(len);
    // C cast is required below
    return os.read((void*)(rhs.data()), len);
}
VerilatedSerialize& operator<<(VerilatedSerialize& os, VerilatedContext* rhsp);
VerilatedDeserialize& operator>>(VerilatedDeserialize& os, VerilatedContext* rhsp);

template <class T_Key, class T_Value>
VerilatedSerialize& operator<<(VerilatedSerialize& os, VlAssocArray<T_Key, T_Value>& rhs) {
    os << rhs.atDefault();
    const uint32_t len = rhs.size();
    os << len;
    for (const auto& i : rhs) {
        const T_Key index = i.first;  // Copy to get around const_iterator
        const T_Value value = i.second;
        os << index << value;
    }
    return os;
}
template <class T_Key, class T_Value>
VerilatedDeserialize& operator>>(VerilatedDeserialize& os, VlAssocArray<T_Key, T_Value>& rhs) {
    os >> rhs.atDefault();
    uint32_t len = 0;
    os >> len;
    rhs.clear();
    for (uint32_t i = 0; i < len; ++i) {
        T_Key index;
        T_Value value;
        os >> index;
        os >> value;
        rhs.at(index) = value;
    }
    return os;
}

#endif  // Guard
