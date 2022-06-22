// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Large 4-state numbers
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

#ifndef VERILATOR_V3NUMBER_H_
#define VERILATOR_V3NUMBER_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Hash.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdlib>
#include <limits>
#include <memory>
#include <vector>

//============================================================================

// Return if two numbers within Epsilon of each other
inline bool v3EpsilonEqual(double a, double b) {
    return std::fabs(a - b)
           <= (std::numeric_limits<double>::epsilon() * std::max(1.0, std::max(a, b)));
}

//============================================================================

class AstNode;
class AstNodeDType;
class FileLine;

// Holds a few entries of ValueAndX (32 four-state bits) in-place and uses heap-allocated buffer
// when more is needed.
class V3NumberFourStateArray final {
public:
    // TYPES
    struct ValueAndX final {
        // Value, with bit 0 in bit 0 of this vector (unless X/Z)
        uint32_t m_value;
        // Each bit is true if it's X or Z, 10=z, 11=x
        uint32_t m_valueX;
        bool operator==(const ValueAndX& other) const {
            return m_value == other.m_value && m_valueX == other.m_valueX;
        }
    };

    struct ValueAndXArrayDeleter {
        // Using free() because the array uses realloc() for allocations.
        void operator()(ValueAndX* ptr) const { std::free(ptr); }
    };
    using ValueAndXArrayPtr = std::unique_ptr<ValueAndX[], ValueAndXArrayDeleter>;

    // MEMBERS
    // Hold at least 64 bits without dynamic allocation. In most cases it will be 96 bits
    // (std::string usually has 32 bytes).
    static constexpr size_t m_inlinedSize
        = std::max<size_t>(2, (sizeof(string) - sizeof(ValueAndXArrayPtr)) / sizeof(ValueAndX));
    ValueAndX m_inlined[m_inlinedSize];  // Holds the beginning m_inlinedSize words
    ValueAndXArrayPtr m_dynamic;  // Holds m_inlinedSize-th word and later

public:
    // CONSTRUCTORS
    V3NumberFourStateArray() {
        for (size_t i = 0; i < m_inlinedSize; ++i) m_inlined[i] = {0, 0};
    }

    V3NumberFourStateArray(const V3NumberFourStateArray&) = delete;
    V3NumberFourStateArray& operator=(const V3NumberFourStateArray&) = delete;

    V3NumberFourStateArray(size_t wordsCount, const V3NumberFourStateArray& other) {
        resize(wordsCount);
        for (size_t i = 0; i < (wordsCount > m_inlinedSize ? wordsCount : m_inlinedSize); ++i)
            (*this)[i] = other[i];
    }

    V3NumberFourStateArray& copyFrom(size_t wordsCount, const V3NumberFourStateArray& other) {
        resize(wordsCount);
        for (size_t i = 0; i < (wordsCount > m_inlinedSize ? wordsCount : m_inlinedSize); ++i)
            (*this)[i] = other[i];
        return *this;
    }

    V3NumberFourStateArray(V3NumberFourStateArray&& other)
        : m_dynamic(std::move(other.m_dynamic)) {
        for (size_t i = 0; i < m_inlinedSize; ++i) m_inlined[i] = other[i];
    }

    V3NumberFourStateArray& operator=(V3NumberFourStateArray&& other) {
        for (size_t i = 0; i < m_inlinedSize; ++i) m_inlined[i] = other[i];
        m_dynamic = std::move(other.m_dynamic);
        return *this;
    }

    ~V3NumberFourStateArray() = default;

    // METHODS
    void resize(size_t wordsCount) {
        if (wordsCount <= m_inlinedSize) {
            m_dynamic.reset(nullptr);
        } else {
            const std::size_t dynamicWordsCount = wordsCount - m_inlinedSize;
            ValueAndX* const oldPtr = m_dynamic.release();
            // (Re)allocation with realloc allows for:
            // - Increasing the buffer size without data loss when current size is not explicitly
            //   known.
            // - A chance of buffer resizing without moving it.
            void* const ptr = std::realloc(oldPtr, sizeof(ValueAndX) * dynamicWordsCount);
            m_dynamic.reset(reinterpret_cast<ValueAndX*>(ptr));
        }
    }

    ValueAndX& operator[](size_t idx) {
        return idx >= m_inlinedSize ? m_dynamic[idx - m_inlinedSize] : m_inlined[idx];
    }
    const ValueAndX& operator[](size_t idx) const {
        return const_cast<V3NumberFourStateArray&>(*this)[idx];
    }
};

enum class V3NumberDataType : uint8_t {
    UNINITIALIZED = 0,
    STRING = 1,
    DOUBLE = 2,
    LOGIC = 3,
};
inline std::ostream& operator<<(std::ostream& os, const V3NumberDataType& rhs) {
    switch (rhs) {
    case V3NumberDataType::UNINITIALIZED: return os << "UNINITIALIZED";
    case V3NumberDataType::STRING: return os << "STRING";
    case V3NumberDataType::DOUBLE: return os << "DOUBLE";
    case V3NumberDataType::LOGIC: return os << "LOGIC";
    }
    return os;
}

class V3NumberData final {
    // MEMBERS
    union {
        uint8_t m_uninitializedMemberDoNotUse;  // Dummy member to avoid automatic initialization.
        V3NumberFourStateArray m_number;
        std::string m_string;
    };

    int m_width = 0;  // Width (in bits) as specified/calculated
    V3NumberDataType m_type : 2;

public:
    bool m_sized : 1;  // True if the user specified the width, else we track it.
    bool m_signed : 1;  // True if signed value
    bool m_isNull : 1;  // True if "null" versus normal 0
    bool m_fromString : 1;  // True if from string literal
    bool m_autoExtend : 1;  // True if SystemVerilog extend-to-any-width

public:
    // CONSTRUCTORS
    V3NumberData()
        : m_type{V3NumberDataType::UNINITIALIZED}
        , m_sized{false}
        , m_signed{false}
        , m_isNull{false}
        , m_fromString{false}
        , m_autoExtend{false} {}

    ~V3NumberData() {
        if (isNumber())
            destroyNumber();
        else if (isString())
            destroyString();
    }

    V3NumberData(const V3NumberData& other)
        : m_width{other.m_width}
        , m_type{other.m_type}
        , m_sized{other.m_sized}
        , m_signed{other.m_signed}
        , m_isNull{other.m_isNull}
        , m_fromString{other.m_fromString}
        , m_autoExtend{other.m_autoExtend} {
        switch (other.m_type) {
        case V3NumberDataType::STRING: initString(other.m_string); break;
        case V3NumberDataType::DOUBLE:  // FALLTHRU
        case V3NumberDataType::LOGIC:
            initNumber(bitsToWords(other.m_width), other.m_number);
            break;
        case V3NumberDataType::UNINITIALIZED: break;
        }
    }

    V3NumberData& operator=(const V3NumberData& other) {
        switch (other.m_type) {
        case V3NumberDataType::STRING: reinitWithOrAssignString(other.m_string); break;
        case V3NumberDataType::DOUBLE:  // FALLTHRU
        case V3NumberDataType::LOGIC:
            if (isNumber()) {
                m_number.copyFrom(bitsToWords(other.m_width), other.m_number);
            } else {
                if (isString()) destroyString();
                initNumber(bitsToWords(other.m_width), other.m_number);
            }
            break;
        case V3NumberDataType::UNINITIALIZED:
            if (isNumber())
                destroyNumber();
            else if (isString())
                destroyString();
            break;
        }
        m_width = other.m_width;
        m_type = other.m_type;
        m_sized = other.m_sized;
        m_signed = other.m_signed;
        m_isNull = other.m_isNull;
        m_fromString = other.m_fromString;
        m_autoExtend = other.m_autoExtend;
        return *this;
    }

    V3NumberData(V3NumberData&& other)
        : m_width{other.m_width}
        , m_type{other.m_type}
        , m_sized{other.m_sized}
        , m_signed{other.m_signed}
        , m_isNull{other.m_isNull}
        , m_fromString{other.m_fromString}
        , m_autoExtend{other.m_autoExtend} {
        switch (other.m_type) {
        case V3NumberDataType::STRING: initString(std::move(other.m_string)); break;
        case V3NumberDataType::DOUBLE:  // FALLTHRU
        case V3NumberDataType::LOGIC: initNumber(std::move(other.m_number)); break;
        case V3NumberDataType::UNINITIALIZED: break;
        }
        other.m_type = V3NumberDataType::UNINITIALIZED;
    }

    V3NumberData& operator=(V3NumberData&& other) {
        switch (other.m_type) {
        case V3NumberDataType::STRING: reinitWithOrAssignString(std::move(other.m_string)); break;
        case V3NumberDataType::DOUBLE:  // FALLTHRU
        case V3NumberDataType::LOGIC:
            if (isNumber()) {
                m_number = std::move(other.m_number);
            } else {
                if (isString()) destroyString();
                initNumber(std::move(other.m_number));
            }
            break;
        case V3NumberDataType::UNINITIALIZED:
            if (isNumber())
                destroyNumber();
            else if (isString())
                destroyString();
            break;
        }
        m_width = other.m_width;
        m_type = other.m_type;
        m_sized = other.m_sized;
        m_signed = other.m_signed;
        m_isNull = other.m_isNull;
        m_fromString = other.m_fromString;
        m_autoExtend = other.m_autoExtend;
        other.m_type = V3NumberDataType::UNINITIALIZED;
        return *this;
    }

    // ACCESSORS
    inline V3NumberFourStateArray& num() {
        UASSERT(isNumber(), "`num` member accessed when data type is " << m_type);
        return m_number;
    }
    inline const V3NumberFourStateArray& num() const {
        UASSERT(isNumber(), "`num` member accessed when data type is " << m_type);
        return m_number;
    }
    inline std::string& str() {
        UASSERT(isString(), "`str` member accessed when data type is " << m_type);
        return m_string;
    }
    inline const std::string& str() const {
        UASSERT(isString(), "`str` member accessed when data type is " << m_type);
        return m_string;
    }

    int width() const { return m_width; }
    V3NumberDataType type() const { return m_type; }

    // METHODS
    void resize(int bitsCount) {
        if (m_width == bitsCount) return;
        if (isNumber() && bitsToWords(m_width) != bitsToWords(bitsCount)) {
            m_number.resize(bitsToWords(bitsCount));
        }
        m_width = bitsCount;
    }

    void setString() {
        // If there has been a string already it is kept intact.
        if (isString()) return;
        if (isNumber()) destroyNumber();
        initString();
        m_type = V3NumberDataType::STRING;
    }
    void setString(std::string&& s) {
        reinitWithOrAssignString(std::move(s));
        m_type = V3NumberDataType::STRING;
    }
    void setString(const std::string& s) {
        reinitWithOrAssignString(s);
        m_type = V3NumberDataType::STRING;
    }

    void setDouble() {
        if (isString()) destroyString();
        if (!isNumber()) initNumber();
        m_type = V3NumberDataType::DOUBLE;
        resize(64);
        // If there has been a number (logic or double) already its lower 64 bits are kept intact.
    }

    void setLogic() {
        if (isString()) destroyString();
        if (!isNumber()) initNumber();
        m_type = V3NumberDataType::LOGIC;
        resize(m_width);
        // If there has been a number (logic or double) already its bits are kept intact.
    }

private:
    static constexpr int bitsToWords(int bitsCount) { return (bitsCount + 31) / 32; }

    inline bool isNumber() const {
        return m_type == V3NumberDataType::DOUBLE || m_type == V3NumberDataType::LOGIC;
    }
    inline bool isString() const { return m_type == V3NumberDataType::STRING; }

    template <typename... Args>
    inline void initNumber(Args&&... args) {
        new (&m_number) V3NumberFourStateArray(std::forward<Args>(args)...);
    }
    template <typename... Args>
    inline void initString(Args&&... args) {
        new (&m_string) std::string(std::forward<Args>(args)...);
    }

    inline void destroyNumber() { m_number.~V3NumberFourStateArray(); }
    inline void destroyString() { m_string.~string(); }

    template <typename T>
    inline void reinitWithOrAssignString(T&& s) {
        if (isString()) {
            m_string = std::forward<T>(s);
            return;
        }
        if (isNumber()) destroyNumber();
        initString(std::forward<T>(s));
    }
};

class V3Number final {
    // TYPES
    using ValueAndX = V3NumberFourStateArray::ValueAndX;

    V3NumberData m_data;
    AstNode* m_nodep;  // Parent node
    FileLine* m_fileline;

    // METHODS
    V3Number& setSingleBits(char value);
    V3Number& setString(const string& str) {
        m_data.setString(str);
        return *this;
    }
    void opCleanThis(bool warnOnTruncation = false);

public:
    void nodep(AstNode* nodep) { setNames(nodep); }
    FileLine* fileline() const { return m_fileline; }
    V3Number& setZero();
    V3Number& setQuad(uint64_t value);
    V3Number& setLong(uint32_t value);
    V3Number& setLongS(int32_t value);
    V3Number& setDouble(double value);
    void setBit(int bit, char value) {  // Note: must be initialized as number and pre-zeroed!
        if (bit >= m_data.width()) return;
        const uint32_t mask = (1UL << (bit & 31));
        ValueAndX& v = m_data.num()[bit / 32];
        if (value == '0' || value == 0) {
            v.m_value &= ~mask;
            v.m_valueX &= ~mask;
        } else if (value == '1' || value == 1) {
            v.m_value |= mask;
            v.m_valueX &= ~mask;
        } else if (value == 'z' || value == 2) {
            v.m_value &= ~mask;
            v.m_valueX |= mask;
        } else {  // X
            v.m_value |= mask;
            v.m_valueX |= mask;
        }
    }

private:
    char bitIs(int bit) const {
        if (bit >= m_data.width() || bit < 0) {
            // We never sign extend
            return '0';
        }
        const ValueAndX v = m_data.num()[bit / 32];
        return ("01zx"[(((v.m_value & (1UL << (bit & 31))) ? 1 : 0)
                        | ((v.m_valueX & (1UL << (bit & 31))) ? 2 : 0))]);
    }
    char bitIsExtend(int bit, int lbits) const {
        // lbits usually = width, but for C optimizations width=32_bits, lbits = 32_or_less
        if (bit < 0) return '0';
        UASSERT(lbits <= m_data.width(), "Extend of wrong size");
        if (bit >= lbits) {
            bit = lbits ? lbits - 1 : 0;
            const ValueAndX v = m_data.num()[bit / 32];
            // We do sign extend
            return ("01zx"[(((v.m_value & (1UL << (bit & 31))) ? 1 : 0)
                            | ((v.m_valueX & (1UL << (bit & 31))) ? 2 : 0))]);
        }
        const ValueAndX v = m_data.num()[bit / 32];
        return ("01zx"[(((v.m_value & (1UL << (bit & 31))) ? 1 : 0)
                        | ((v.m_valueX & (1UL << (bit & 31))) ? 2 : 0))]);
    }

public:
    bool bitIs0(int bit) const {
        if (!isNumber()) return false;
        if (bit < 0) return false;
        if (bit >= m_data.width()) return !bitIsXZ(m_data.width() - 1);
        const ValueAndX v = m_data.num()[bit / 32];
        return ((v.m_value & (1UL << (bit & 31))) == 0 && !(v.m_valueX & (1UL << (bit & 31))));
    }
    bool bitIs1(int bit) const {
        if (!isNumber()) return false;
        if (bit < 0) return false;
        if (bit >= m_data.width()) return false;
        const ValueAndX v = m_data.num()[bit / 32];
        return ((v.m_value & (1UL << (bit & 31))) && !(v.m_valueX & (1UL << (bit & 31))));
    }
    bool bitIs1Extend(int bit) const {
        if (!isNumber()) return false;
        if (bit < 0) return false;
        if (bit >= m_data.width()) return bitIs1Extend(m_data.width() - 1);
        const ValueAndX v = m_data.num()[bit / 32];
        return ((v.m_value & (1UL << (bit & 31))) && !(v.m_valueX & (1UL << (bit & 31))));
    }
    bool bitIsX(int bit) const {
        if (!isNumber()) return false;
        if (bit < 0) return false;
        if (bit >= m_data.width()) return bitIsZ(m_data.width() - 1);
        const ValueAndX v = m_data.num()[bit / 32];
        return ((v.m_value & (1UL << (bit & 31))) && (v.m_valueX & (1UL << (bit & 31))));
    }
    bool bitIsXZ(int bit) const {
        if (!isNumber()) return false;
        if (bit < 0) return false;
        if (bit >= m_data.width()) return bitIsXZ(m_data.width() - 1);
        const ValueAndX v = m_data.num()[bit / 32];
        return ((v.m_valueX & (1UL << (bit & 31))));
    }
    bool bitIsZ(int bit) const {
        if (!isNumber()) return false;
        if (bit < 0) return false;
        if (bit >= m_data.width()) return bitIsZ(m_data.width() - 1);
        const ValueAndX v = m_data.num()[bit / 32];
        return ((~v.m_value & (1UL << (bit & 31))) && (v.m_valueX & (1UL << (bit & 31))));
    }

private:
    uint32_t bitsValue(int lsb, int nbits) const {
        uint32_t v = 0;
        for (int bitn = 0; bitn < nbits; bitn++) { v |= (bitIs1(lsb + bitn) << bitn); }
        return v;
    }

    int countX(int lsb, int nbits) const;
    int countZ(int lsb, int nbits) const;

    int words() const { return ((width() + 31) / 32); }
    uint32_t hiWordMask() const { return VL_MASK_I(width()); }

    V3Number& opModDivGuts(const V3Number& lhs, const V3Number& rhs, bool is_modulus);

public:
    // CONSTRUCTORS
    explicit V3Number(AstNode* nodep) { init(nodep, 1); }
    V3Number(AstNode* nodep, int width) {  // 0=unsized
        init(nodep, std::max(width, 1), width > 0);
    }
    V3Number(AstNode* nodep, int width, uint32_t value, bool sized = true) {
        UASSERT(width > 0, "Width must be a positive number.");
        init(nodep, width, sized);
        m_data.num()[0].m_value = value;
        opCleanThis();
    }
    // Create from a verilog 32'hxxxx number.
    V3Number(AstNode* nodep, const char* sourcep) { V3NumberCreate(nodep, sourcep, nullptr); }
    class FileLined {};  // Fileline based errors, for parsing only, otherwise pass nodep
    V3Number(FileLined, FileLine* fl, const char* sourcep) {
        V3NumberCreate(nullptr, sourcep, fl);
    }
    class VerilogStringLiteral {};  // For creator type-overload selection
    V3Number(VerilogStringLiteral, AstNode* nodep, const string& str);
    class String {};
    V3Number(String, AstNode* nodep, const string& value) {
        init(nodep, 0);
        setString(value);
        m_data.m_fromString = true;
    }
    class Null {};
    V3Number(Null, AstNode* nodep) {
        init(nodep, 0);
        m_data.setLogic();
        m_data.m_isNull = true;
        m_data.m_autoExtend = true;
    }
    explicit V3Number(const V3Number* nump, int width = 1) {
        init(nullptr, width);
        m_fileline = nump->fileline();
    }
    V3Number(const V3Number* nump, int width, uint32_t value) {
        init(nullptr, width);
        m_data.num()[0].m_value = value;
        opCleanThis();
        m_fileline = nump->fileline();
    }
    V3Number(AstNode* nodep, double value) {
        init(nodep, 64);
        setDouble(value);
    }
    V3Number(AstNode* nodep, const AstNodeDType* nodedtypep);

    V3Number(const V3Number& other) = default;
    V3Number& operator=(const V3Number& other) = default;

    V3Number(V3Number&& other) = default;
    V3Number& operator=(V3Number&& other) = default;

    ~V3Number() {}

private:
    void V3NumberCreate(AstNode* nodep, const char* sourcep, FileLine* fl);
    void init(AstNode* nodep, int swidth, bool sized = true) {
        setNames(nodep);
        if (swidth) {
            m_data.setLogic();
            m_data.resize(swidth);
            m_data.m_sized = sized;
            for (int i = 0; i < words(); ++i) m_data.num()[i] = {0, 0};
        } else {
            m_data.resize(1);
            m_data.m_sized = false;
        }
    }
    void setNames(AstNode* nodep);
    static string displayPad(size_t fmtsize, char pad, bool left, const string& in);
    string displayed(FileLine* fl, const string& vformat) const;
    string displayed(const string& vformat) const { return displayed(m_fileline, vformat); }

public:
    void v3errorEnd(std::ostringstream& sstr) const;
    void v3errorEndFatal(std::ostringstream& sstr) const VL_ATTR_NORETURN;
    void width(int width, bool sized = true) {
        m_data.m_sized = sized;
        m_data.resize(width);
    }

    // SETTERS
    V3Number& setAllBitsXRemoved();
    V3Number& setAllBitsX();
    V3Number& setAllBitsZ();
    V3Number& setAllBits0();
    V3Number& setAllBits1();
    V3Number& setMask(int nbits);  // IE if nbits=1, then 0b1, if 2->0b11, if 3->0b111 etc

    // ACCESSORS
    string ascii(bool prefixed = true, bool cleanVerilog = false) const;
    string displayed(AstNode* nodep, const string& vformat) const;
    static bool displayedFmtLegal(char format, bool isScan);  // Is this a valid format letter?
    int width() const { return m_data.width(); }
    int widthMin() const;  // Minimum width that can represent this number (~== log2(num)+1)
    bool sized() const { return m_data.m_sized; }
    bool autoExtend() const { return m_data.m_autoExtend; }
    bool isFromString() const { return m_data.m_fromString; }
    V3NumberDataType dataType() const { return m_data.type(); }
    void dataType(V3NumberDataType newType) {
        if (dataType() == newType) return;
        UASSERT(newType != V3NumberDataType::UNINITIALIZED, "Can't set type to UNINITIALIZED.");
        switch (newType) {
        case V3NumberDataType::STRING: m_data.setString(); break;
        case V3NumberDataType::DOUBLE: m_data.setDouble(); break;
        case V3NumberDataType::LOGIC: m_data.setLogic(); break;
        case V3NumberDataType::UNINITIALIZED: break;
        }
    }
    // Only correct for parsing of numbers from strings, otherwise not used
    // (use AstConst::isSigned())
    bool isSigned() const { return m_data.m_signed; }
    void isSigned(bool ssigned) { m_data.m_signed = ssigned; }
    bool isDouble() const { return dataType() == V3NumberDataType::DOUBLE; }
    bool isString() const { return dataType() == V3NumberDataType::STRING; }
    bool isNumber() const {
        return m_data.type() == V3NumberDataType::LOGIC
               || m_data.type() == V3NumberDataType::DOUBLE;
    }
    bool isNegative() const { return !isString() && bitIs1(width() - 1); }
    bool isNull() const { return m_data.m_isNull; }
    bool isFourState() const;
    bool hasZ() const {
        if (isString()) return false;
        for (int i = 0; i < words(); i++) {
            const ValueAndX v = m_data.num()[i];
            if ((~v.m_value) & v.m_valueX) return true;
        }
        return false;
    }
    bool isAllZ() const;
    bool isAllX() const;
    bool isEqZero() const;
    bool isNeqZero() const;
    bool isBitsZero(int msb, int lsb) const;
    bool isEqOne() const;
    bool isEqAllOnes(int optwidth = 0) const;
    bool isCaseEq(const V3Number& rhs) const;  // operator==
    bool isLtXZ(const V3Number& rhs) const;  // operator< with XZ compared
    bool isAnyX() const;
    bool isAnyXZ() const;
    bool isAnyZ() const;
    bool isMsbXZ() const { return bitIsXZ(m_data.width() - 1); }
    uint32_t toUInt() const;
    int32_t toSInt() const;
    uint64_t toUQuad() const;
    int64_t toSQuad() const;
    string toString() const;
    string toDecimalS() const;  // return ASCII signed decimal number
    string toDecimalU() const;  // return ASCII unsigned decimal number
    double toDouble() const;
    V3Hash toHash() const;
    uint32_t edataWord(int eword) const;
    uint8_t dataByte(int byte) const;
    uint32_t countBits(const V3Number& ctrl) const;
    uint32_t countBits(const V3Number& ctrl1, const V3Number& ctrl2, const V3Number& ctrl3) const;
    uint32_t countOnes() const;
    uint32_t
    mostSetBitP1() const;  // Highest bit set plus one, IE for 16 return 5, for 0 return 0.

    // Operators
    bool operator<(const V3Number& rhs) const { return isLtXZ(rhs); }

    // STATICS
    static int log2b(uint32_t num);

    // MATH
    // "this" is the output, as we need the output width before some computations
    V3Number& opBitsNonX(const V3Number& lhs);  // 0/1->1, X/Z->0
    V3Number& opBitsOne(const V3Number& lhs);  // 1->1, 0/X/Z->0
    V3Number& opBitsXZ(const V3Number& lhs);  // 0/1->0, X/Z->1
    V3Number& opBitsZ(const V3Number& lhs);  // Z->1, 0/1/X->0
    V3Number& opBitsNonZ(const V3Number& lhs);  // Z->0, 0/1/X->1
    //
    V3Number& opAssign(const V3Number& lhs);
    V3Number& opAssignNonXZ(const V3Number& lhs, bool ignoreXZ = true);
    V3Number& opExtendS(const V3Number& lhs, uint32_t lbits);  // Sign extension
    V3Number& opExtendXZ(const V3Number& lhs, uint32_t lbits);  // X/Z extension
    V3Number& opRedOr(const V3Number& lhs);
    V3Number& opRedAnd(const V3Number& lhs);
    V3Number& opRedXor(const V3Number& lhs);
    V3Number& opCountBits(const V3Number& expr, const V3Number& ctrl1, const V3Number& ctrl2,
                          const V3Number& ctrl3);
    V3Number& opCountOnes(const V3Number& lhs);
    V3Number& opIsUnknown(const V3Number& lhs);
    V3Number& opOneHot(const V3Number& lhs);
    V3Number& opOneHot0(const V3Number& lhs);
    V3Number& opCLog2(const V3Number& lhs);
    V3Number& opClean(const V3Number& lhs, uint32_t bits);
    V3Number& opConcat(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLenN(const V3Number& lhs);
    V3Number& opRepl(const V3Number& lhs, const V3Number& rhs);
    V3Number& opRepl(const V3Number& lhs, uint32_t rhsval);
    V3Number& opStreamL(const V3Number& lhs, const V3Number& rhs);
    V3Number& opSel(const V3Number& lhs, const V3Number& msb, const V3Number& lsb);
    V3Number& opSel(const V3Number& lhs, uint32_t msbval, uint32_t lsbval);
    V3Number& opSelInto(const V3Number& lhs, const V3Number& lsb, int width);
    V3Number& opSelInto(const V3Number& lhs, int lsbval, int width);
    V3Number& opToLowerN(const V3Number& lhs);
    V3Number& opToUpperN(const V3Number& lhs);
    V3Number& opCaseEq(const V3Number& lhs, const V3Number& rhs);
    V3Number& opCaseNeq(const V3Number& lhs, const V3Number& rhs);
    V3Number& opWildEq(const V3Number& lhs, const V3Number& rhs);
    V3Number& opWildNeq(const V3Number& lhs, const V3Number& rhs);
    V3Number& opBufIf1(const V3Number& ens, const V3Number& if1s);
    // "standard" math
    V3Number& opNot(const V3Number& lhs);
    V3Number& opLogNot(const V3Number& lhs);
    V3Number& opLogAnd(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLogOr(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLogEq(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLogIf(const V3Number& lhs, const V3Number& rhs);
    V3Number& opNegate(const V3Number& lhs);
    V3Number& opAdd(const V3Number& lhs, const V3Number& rhs);
    V3Number& opSub(const V3Number& lhs, const V3Number& rhs);
    V3Number& opMul(const V3Number& lhs, const V3Number& rhs);
    V3Number& opMulS(const V3Number& lhs, const V3Number& rhs);  // Signed
    V3Number& opDiv(const V3Number& lhs, const V3Number& rhs);
    V3Number& opDivS(const V3Number& lhs, const V3Number& rhs);  // Signed
    V3Number& opModDiv(const V3Number& lhs, const V3Number& rhs);
    V3Number& opModDivS(const V3Number& lhs, const V3Number& rhs);  // Signed
    V3Number& opPow(const V3Number& lhs, const V3Number& rhs, bool lsign = false,
                    bool rsign = false);
    V3Number& opPowSU(const V3Number& lhs, const V3Number& rhs);  // Signed lhs, unsigned rhs
    V3Number& opPowSS(const V3Number& lhs, const V3Number& rhs);  // Signed lhs, signed rhs
    V3Number& opPowUS(const V3Number& lhs, const V3Number& rhs);  // Unsigned lhs, signed rhs
    V3Number& opAnd(const V3Number& lhs, const V3Number& rhs);
    V3Number& opXor(const V3Number& lhs, const V3Number& rhs);
    V3Number& opOr(const V3Number& lhs, const V3Number& rhs);
    V3Number& opShiftR(const V3Number& lhs, const V3Number& rhs);
    V3Number& opShiftRS(const V3Number& lhs, const V3Number& rhs,  // Arithmetic w/carry
                        uint32_t lbits);
    V3Number& opShiftL(const V3Number& lhs, const V3Number& rhs);
    // Comparisons
    V3Number& opEq(const V3Number& lhs, const V3Number& rhs);
    V3Number& opNeq(const V3Number& lhs, const V3Number& rhs);
    V3Number& opGt(const V3Number& lhs, const V3Number& rhs);
    V3Number& opGtS(const V3Number& lhs, const V3Number& rhs);  // Signed
    V3Number& opGte(const V3Number& lhs, const V3Number& rhs);
    V3Number& opGteS(const V3Number& lhs, const V3Number& rhs);  // Signed
    V3Number& opLt(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLtS(const V3Number& lhs, const V3Number& rhs);  // Signed
    V3Number& opLte(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLteS(const V3Number& lhs, const V3Number& rhs);  // Signed

    // "D" - double (aka real) math
    V3Number& opIToRD(const V3Number& lhs, bool isSigned = false);
    V3Number& opISToRD(const V3Number& lhs) { return opIToRD(lhs, true); }
    V3Number& opRToIS(const V3Number& lhs);
    V3Number& opRToIRoundS(const V3Number& lhs);
    V3Number& opRealToBits(const V3Number& lhs);
    V3Number& opBitsToRealD(const V3Number& lhs);
    V3Number& opNegateD(const V3Number& lhs);
    V3Number& opAddD(const V3Number& lhs, const V3Number& rhs);
    V3Number& opSubD(const V3Number& lhs, const V3Number& rhs);
    V3Number& opMulD(const V3Number& lhs, const V3Number& rhs);
    V3Number& opDivD(const V3Number& lhs, const V3Number& rhs);
    V3Number& opPowD(const V3Number& lhs, const V3Number& rhs);
    // Comparisons
    V3Number& opEqD(const V3Number& lhs, const V3Number& rhs);
    V3Number& opNeqD(const V3Number& lhs, const V3Number& rhs);
    V3Number& opGtD(const V3Number& lhs, const V3Number& rhs);
    V3Number& opGteD(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLtD(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLteD(const V3Number& lhs, const V3Number& rhs);

    // "N" - string operations
    V3Number& opAtoN(const V3Number& lhs, int base);
    V3Number& opPutcN(const V3Number& lhs, const V3Number& rhs, const V3Number& ths);
    V3Number& opGetcN(const V3Number& lhs, const V3Number& rhs);
    V3Number& opSubstrN(const V3Number& lhs, const V3Number& rhs, const V3Number& ths);
    V3Number& opCompareNN(const V3Number& lhs, const V3Number& rhs, bool ignoreCase);
    V3Number& opConcatN(const V3Number& lhs, const V3Number& rhs);
    V3Number& opReplN(const V3Number& lhs, const V3Number& rhs);
    V3Number& opReplN(const V3Number& lhs, uint32_t rhsval);
    V3Number& opEqN(const V3Number& lhs, const V3Number& rhs);
    V3Number& opNeqN(const V3Number& lhs, const V3Number& rhs);
    V3Number& opGtN(const V3Number& lhs, const V3Number& rhs);
    V3Number& opGteN(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLtN(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLteN(const V3Number& lhs, const V3Number& rhs);
};
inline std::ostream& operator<<(std::ostream& os, const V3Number& rhs) {
    return os << rhs.ascii();
}

#endif  // Guard
