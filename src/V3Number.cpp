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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Number.h"

#include "V3Ast.h"
#include "V3Global.h"

#include <algorithm>
#include <cerrno>
#include <cmath>
#include <functional>

constexpr int MAX_SPRINTF_DOUBLE_SIZE
    = 1100;  // Maximum characters with a sprintf %e/%f/%g (really 1079)

// Number operations build output in-place so can't call e.g. foo.opX(foo)
#define NUM_ASSERT_OP_ARGS1(arg1) \
    UASSERT((this != &(arg1)), "Number operation called with same source and dest")
#define NUM_ASSERT_OP_ARGS2(arg1, arg2) \
    UASSERT((this != &(arg1) && this != &(arg2)), \
            "Number operation called with same source and dest")
#define NUM_ASSERT_OP_ARGS3(arg1, arg2, arg3) \
    UASSERT((this != &(arg1) && this != &(arg2) && this != &(arg3)), \
            "Number operation called with same source and dest")
#define NUM_ASSERT_OP_ARGS4(arg1, arg2, arg3, arg4) \
    UASSERT((this != &(arg1) && this != &(arg2) && this != &(arg3) && this != &(arg4)), \
            "Number operation called with same source and dest")

#define NUM_ASSERT_LOGIC_ARGS1(arg1) \
    UASSERT((!(arg1).isDouble() && !(arg1).isString()), \
            "Number operation called with non-logic (double or string) argument: '" << (arg1) \
                                                                                    << '"')
#define NUM_ASSERT_LOGIC_ARGS2(arg1, arg2) \
    NUM_ASSERT_LOGIC_ARGS1(arg1); \
    NUM_ASSERT_LOGIC_ARGS1(arg2)

#define NUM_ASSERT_LOGIC_ARGS4(arg1, arg2, arg3, arg4) \
    NUM_ASSERT_LOGIC_ARGS1(arg1); \
    NUM_ASSERT_LOGIC_ARGS1(arg2); \
    NUM_ASSERT_LOGIC_ARGS1(arg3); \
    NUM_ASSERT_LOGIC_ARGS1(arg4)

#define NUM_ASSERT_STRING_ARGS1(arg1) \
    UASSERT((arg1).isString(), \
            "Number operation called with non-string argument: '" << (arg1) << '"')
#define NUM_ASSERT_STRING_ARGS2(arg1, arg2) \
    NUM_ASSERT_STRING_ARGS1(arg1); \
    NUM_ASSERT_STRING_ARGS1(arg2)

#define NUM_ASSERT_DOUBLE_ARGS1(arg1) \
    UASSERT((arg1).isDouble(), \
            "Number operation called with non-double argument: '" << (arg1) << '"')
#define NUM_ASSERT_DOUBLE_ARGS2(arg1, arg2) \
    NUM_ASSERT_DOUBLE_ARGS1(arg1); \
    NUM_ASSERT_DOUBLE_ARGS1(arg2)

//======================================================================
// Errors

void V3Number::v3errorEnd(std::ostringstream& str) const {
    std::ostringstream nsstr;
    nsstr << str.str();
    if (m_nodep) {
        m_nodep->v3errorEnd(nsstr);
    } else {
        m_fileline->v3errorEnd(nsstr);
    }
}

void V3Number::v3errorEndFatal(std::ostringstream& str) const {
    v3errorEnd(str);
    assert(0);  // LCOV_EXCL_LINE
    VL_UNREACHABLE
}

//======================================================================
// Read class functions
// CREATION

V3Number::V3Number(VerilogStringLiteral, AstNode* nodep, const string& str) {
    // Create a number using a verilog string as the value, thus 8 bits per character.
    // cppcheck bug - doesn't see init() resets these
    // cppcheck: Member variable 'm_sized/m_width' is not initialized in the constructor
    init(nodep, str.length() * 8);
    m_fromString = true;
    for (unsigned pos = 0; pos < str.length(); ++pos) {
        const int topos = str.length() - 1 - pos;
        ValueAndX& v = m_value[topos / 4];
        for (int bit = 0; bit < 8; ++bit) {
            if (str[pos] & (1UL << bit)) { v.m_value |= (1UL << (bit + (topos % 4) * 8)); }
        }
    }
    opCleanThis(true);
}

V3Number::V3Number(AstNode* nodep, const AstNodeDType* nodedtypep) {
    if (nodedtypep->isString()) {
        init(nodep, 0);
        setString("");
    } else if (nodedtypep->isDouble()) {
        init(nodep, 64);
        setDouble(0.0);
    } else {
        init(nodep, nodedtypep->width(), nodedtypep->widthSized());
    }
}

void V3Number::V3NumberCreate(AstNode* nodep, const char* sourcep, FileLine* fl) {
    init(nodep, 0);
    m_fileline = fl;
    const char* value_startp = sourcep;
    for (const char* cp = sourcep; *cp; cp++) {
        if (*cp == '\'') {
            value_startp = cp + 1;
            break;
        }
    }

    bool unbased = false;
    char base = '\0';
    if (value_startp != sourcep) {  // Has a '
        string widthn;
        const char* cp = sourcep;
        for (; *cp; cp++) {
            if (*cp == '\'') {
                cp++;
                break;
            }
            if (*cp != '_') widthn += *cp;
        }
        while (*cp == '_') cp++;
        if (*cp && tolower(*cp) == 's') {
            cp++;
            isSigned(true);
        }
        if (*cp) {
            base = *cp;
            cp++;
        }
        value_startp = cp;

        if (atoi(widthn.c_str())) {
            if (atoi(widthn.c_str()) < 0 || atoi(widthn.c_str()) > v3Global.opt.maxNumWidth()) {
                // atoi might convert large number to negative, so can't tell which
                v3error("Unsupported: Width of number exceeds implementation limit: "
                        << sourcep << "  (IEEE 1800-2017 6.9.1)");
                width(v3Global.opt.maxNumWidth(), true);
            } else {
                width(atoi(widthn.c_str()), true);
            }
        }
    } else {
        unbased = true;
        base = 'd';
    }

    for (int i = 0; i < words(); ++i) m_value[i] = {0, 0};

    // Special SystemVerilog unsized constructs
    if (base == '0') {
        setBit(0, 0);
        width(1, false);  // So we extend it
        m_autoExtend = true;
    } else if (base == '1') {
        setBit(0, 1);
        width(1, false);  // So we extend it
        m_autoExtend = true;
    } else if (tolower(base) == 'z') {
        setBit(0, 'z');
        width(1, false);  // So we extend it
        m_autoExtend = true;
    } else if (tolower(base) == 'x') {
        setBit(0, 'x');
        width(1, false);  // So we extend it
        m_autoExtend = true;
    }
    // Otherwise...
    else if (!m_sized) {
        width(32, false);  // Says IEEE 1800-2012 5.7.1
        if (unbased) isSigned(true);  // Also says the spec.
    }

    // Ignore leading blanks
    while (*value_startp == '_' || isspace(*value_startp)) value_startp++;
    if (!*value_startp && !m_autoExtend) {
        v3error("Number is missing value digits: " << sourcep);
    }

    int obit = 0;  // Start at LSB
    if (tolower(base) == 'd') {
        // Ignore leading zeros so we don't issue too many digit errors when lots of leading 0's
        while (*value_startp == '_' || *value_startp == '0') value_startp++;
        // Convert decimal number to hex
        int olen = 0;
        uint32_t val = 0;
        int got_x = 0;
        int got_z = 0;
        int got_01 = 0;
        for (const char* cp = value_startp; *cp; cp++) {
            switch (tolower(*cp)) {
            case '0':  // FALLTHRU
            case '1':  // FALLTHRU
            case '2':  // FALLTHRU
            case '3':  // FALLTHRU
            case '4':  // FALLTHRU
            case '5':  // FALLTHRU
            case '6':  // FALLTHRU
            case '7':  // FALLTHRU
            case '8':  // FALLTHRU
            case '9': {
                if (olen <= 7) {  // 10000000 fits in 32 bits, so ok
                    // Constants are common, so for speed avoid wide math until we need it
                    val = val * 10 + (*cp - '0');
                    m_value[0].m_value = val;
                } else {  // Wide; all previous digits are already in m_value[0]
                    // this = (this * 10)/*product*/ + (*cp-'0')/*addend*/
                    // Assumed rare; lots of optimizations are possible here
                    V3Number product(this, width() + 4);  // +4 for overflow detection
                    const V3Number ten(this, width() + 4, 10);
                    const V3Number addend(this, width(), (*cp - '0'));
                    product.opMul(*this, ten);
                    this->opAdd(product, addend);
                    if (product.bitsValue(width(), 4)) {  // Overflowed
                        static int warned = 0;
                        v3error("Too many digits for "
                                << width() << " bit number: " << sourcep << '\n'
                                << ((!m_sized && !warned++) ? (
                                        V3Error::warnMore() + "... As that number was unsized"
                                        + " ('d...) it is limited to 32 bits (IEEE 1800-2017 "
                                          "5.7.1)\n"
                                        + V3Error::warnMore() + "... Suggest adding a size to it.")
                                                            : ""));
                        while (*(cp + 1)) cp++;  // Skip ahead so don't get multiple warnings
                    }
                }
                olen++;
                got_01 = 1;
                break;
            }
            case 'z':
            case '?': {
                got_z = 1;
                setAllBitsZ();
                break;
            }
            case 'x': {
                got_x = 1;
                setAllBitsX();
                break;
            }
            case '_': break;
            default: {
                v3error("Illegal character in decimal constant: " << *cp);
                break;
            }
            }
        }
        obit = width();
        if ((got_01 + got_x + got_z) > 1) {
            v3error("Mixing X/Z/? with digits not legal in decimal constant: " << value_startp);
        }
    } else {
        // Convert bin/octal number to hex
        for (const char* cp = value_startp + strlen(value_startp) - 1; cp >= value_startp; cp--) {
            if (*cp != '_' && *cp != '0' && obit >= width()) {
                v3error("Too many digits for " << width() << " bit number: " << sourcep);
                break;
            }
            switch (tolower(base)) {
            case 'b': {
                switch (tolower(*cp)) {
                case '0': setBit(obit++, 0); break;
                case '1': setBit(obit++, 1); break;
                case 'z':
                case '?': setBit(obit++, 'z'); break;
                case 'x': setBit(obit++, 'x'); break;
                case '_': break;
                default: v3error("Illegal character in binary constant: " << *cp);
                }
                break;
            }

            case 'o':
            case 'c': {
                switch (tolower(*cp)) {
                // clang-format off
                case '0': setBit(obit++, 0); setBit(obit++, 0);  setBit(obit++, 0);  break;
                case '1': setBit(obit++, 1); setBit(obit++, 0);  setBit(obit++, 0);  break;
                case '2': setBit(obit++, 0); setBit(obit++, 1);  setBit(obit++, 0);  break;
                case '3': setBit(obit++, 1); setBit(obit++, 1);  setBit(obit++, 0);  break;
                case '4': setBit(obit++, 0); setBit(obit++, 0);  setBit(obit++, 1);  break;
                case '5': setBit(obit++, 1); setBit(obit++, 0);  setBit(obit++, 1);  break;
                case '6': setBit(obit++, 0); setBit(obit++, 1);  setBit(obit++, 1);  break;
                case '7': setBit(obit++, 1); setBit(obit++, 1);  setBit(obit++, 1);  break;
                case 'z':
                case '?': setBit(obit++, 'z'); setBit(obit++, 'z'); setBit(obit++, 'z'); break;
                case 'x': setBit(obit++, 'x'); setBit(obit++, 'x'); setBit(obit++, 'x'); break;
                case '_': break;
                // clang-format on
                default: v3error("Illegal character in octal constant");
                }
                break;
            }

            case 'h': {
                switch (tolower(*cp)) {
                    // clang-format off
                case '0': setBit(obit++,0); setBit(obit++,0); setBit(obit++,0); setBit(obit++,0); break;
                case '1': setBit(obit++,1); setBit(obit++,0); setBit(obit++,0); setBit(obit++,0); break;
                case '2': setBit(obit++,0); setBit(obit++,1); setBit(obit++,0); setBit(obit++,0); break;
                case '3': setBit(obit++,1); setBit(obit++,1); setBit(obit++,0); setBit(obit++,0); break;
                case '4': setBit(obit++,0); setBit(obit++,0); setBit(obit++,1); setBit(obit++,0); break;
                case '5': setBit(obit++,1); setBit(obit++,0); setBit(obit++,1); setBit(obit++,0); break;
                case '6': setBit(obit++,0); setBit(obit++,1); setBit(obit++,1); setBit(obit++,0); break;
                case '7': setBit(obit++,1); setBit(obit++,1); setBit(obit++,1); setBit(obit++,0); break;
                case '8': setBit(obit++,0); setBit(obit++,0); setBit(obit++,0); setBit(obit++,1); break;
                case '9': setBit(obit++,1); setBit(obit++,0); setBit(obit++,0); setBit(obit++,1); break;
                case 'a': setBit(obit++,0); setBit(obit++,1); setBit(obit++,0); setBit(obit++,1);  break;
                case 'b': setBit(obit++,1); setBit(obit++,1); setBit(obit++,0); setBit(obit++,1); break;
                case 'c': setBit(obit++,0); setBit(obit++,0); setBit(obit++,1); setBit(obit++,1); break;
                case 'd': setBit(obit++,1); setBit(obit++,0); setBit(obit++,1); setBit(obit++,1); break;
                case 'e': setBit(obit++,0); setBit(obit++,1); setBit(obit++,1); setBit(obit++,1); break;
                case 'f': setBit(obit++,1); setBit(obit++,1); setBit(obit++,1); setBit(obit++,1); break;
                case 'z':
                case '?': setBit(obit++,'z'); setBit(obit++,'z'); setBit(obit++,'z'); setBit(obit++,'z'); break;
                case 'x': setBit(obit++,'x'); setBit(obit++,'x'); setBit(obit++,'x'); setBit(obit++,'x'); break;
                    // clang-format on
                case '_': break;
                default: v3error("Illegal character in hex constant: " << *cp);
                }
                break;
            }
            default: v3error("Illegal base character: " << base);
            }
        }
    }

    // Z or X extend specific width values.  Spec says we don't 1 extend.
    // This fixes 2'bx to become 2'bxx.
    while (obit <= width() && obit && bitIsXZ(obit - 1)) {
        setBit(obit, bitIs(obit - 1));
        obit++;
    }
    opCleanThis(true);

    // printf("Dump \"%s\"  CP \"%s\"  B '%c' %d W %d\n", sourcep, value_startp, base, width(),
    // m_value[0]);
}

void V3Number::setNames(AstNode* nodep) {
    m_nodep = nodep;
    if (!nodep) return;
    m_fileline = nodep->fileline();
}

//======================================================================
// Global

int V3Number::log2b(uint32_t num) {
    // See also opCLog2
    for (int bit = 31; bit > 0; bit--) {
        if (num & (1ULL << bit)) return bit;
    }
    return 0;
}

//======================================================================
// Setters

V3Number& V3Number::setZero() {
    for (int i = 0; i < words(); i++) m_value[i] = {0, 0};
    return *this;
}
V3Number& V3Number::setQuad(uint64_t value) {
    for (int i = 0; i < words(); i++) m_value[i] = {0, 0};
    m_value[0].m_value = value & 0xffffffffULL;
    if (width() > 32) m_value[1].m_value = (value >> 32ULL) & 0xffffffffULL;
    opCleanThis();
    return *this;
}
V3Number& V3Number::setLong(uint32_t value) {
    for (int i = 0; i < words(); i++) m_value[i] = {0, 0};
    m_value[0].m_value = value;
    opCleanThis();
    return *this;
}
V3Number& V3Number::setLongS(int32_t value) {
    for (int i = 0; i < words(); i++) m_value[i] = {0, 0};
    union {
        uint32_t u;
        int32_t s;
    } u;
    u.s = value;
    if (u.s) {}
    m_value[0].m_value = u.u;
    opCleanThis();
    return *this;
}
V3Number& V3Number::setDouble(double value) {
    if (VL_UNCOVERABLE(width() != 64)) v3fatalSrc("Real operation on wrong sized number");
    m_double = true;
    union {
        double d;
        uint32_t u[2];
    } u;
    u.d = value;
    if (u.d != 0.0) {}
    for (int i = 2; i < words(); i++) m_value[i] = {0, 0};
    m_value[0].m_value = u.u[0];
    m_value[1].m_value = u.u[1];
    return *this;
}
V3Number& V3Number::setSingleBits(char value) {
    for (int i = 1 /*upper*/; i < words(); i++) m_value[i] = {0, 0};
    m_value[0] = {(value == '1' || value == 'x' || value == 1 || value == 3),
                  (value == 'z' || value == 'x' || value == 2 || value == 3)};
    return *this;
}

V3Number& V3Number::setAllBits0() {
    for (int i = 0; i < words(); i++) m_value[i] = {0, 0};
    return *this;
}
V3Number& V3Number::setAllBits1() {
    for (int i = 0; i < words(); i++) m_value[i] = {~0U, 0};
    opCleanThis();
    return *this;
}
V3Number& V3Number::setAllBitsX() {
    // Use setAllBitsXRemoved if calling this based on a non-X/Z input value such as divide by zero
    for (int i = 0; i < words(); i++) m_value[i] = {~0U, ~0U};
    opCleanThis();
    return *this;
}
V3Number& V3Number::setAllBitsZ() {
    for (int i = 0; i < words(); i++) m_value[i] = {0, ~0U};
    opCleanThis();
    return *this;
}
V3Number& V3Number::setAllBitsXRemoved() {
    if (!v3Global.constRemoveXs()) {
        return setAllBitsX();
    } else {
        // If we get a divide by zero we get Xs.
        // But after V3Unknown we have removed Xs, so use --x-assign to direct-insert 0/1
        if (v3Global.opt.xAssign() == "1") {
            return setAllBits1();
        } else {
            return setAllBits0();
        }
    }
}

V3Number& V3Number::setMask(int nbits) {
    setZero();
    for (int bit = 0; bit < nbits; bit++) setBit(bit, 1);
    return *this;
}

//======================================================================
// ACCESSORS - as strings

string V3Number::ascii(bool prefixed, bool cleanVerilog) const {
    std::ostringstream out;

    if (isDouble()) {
        out.precision(17);
        if (VL_UNCOVERABLE(width() != 64)) {
            out << "%E-bad-width-double";  // LCOV_EXCL_LINE
        } else {
            out << toDouble();
        }
        return out.str();
    } else if (isString()) {
        return '"' + toString() + '"';
    } else {
        if (VL_UNCOVERABLE((m_value[words() - 1].m_value | m_value[words() - 1].m_valueX)
                           & ~hiWordMask())) {
            out << "%E-hidden-bits";  // LCOV_EXCL_LINE
        }
    }
    if (prefixed) {
        if (sized()) {
            out << width() << "'";
        } else if (autoExtend() && !sized() && width() == 1) {
            out << "'";
            if (bitIs0(0)) {
                out << '0';
                if (isNull()) out << "[null]";
            } else if (bitIs1(0)) {
                out << '1';
            } else if (bitIsZ(0)) {
                out << 'z';
            } else {
                out << 'x';
            }
            return out.str();
        } else {
            if (cleanVerilog) {
                out << "'";
            } else {
                out << "?" << width() << "?";
            }
        }
        if (isSigned()) out << "s";
    }

    const bool binary = (isFourState()
#ifdef V3NUMBER_ASCII_BINARY
                         // cppcheck-suppress konwnConditionTrueFalse
                         || true
#endif
    );
    // out<<"-"<<hex<<m_value[0]<<"-";

    // cppcheck-suppress konwnConditionTrueFalse
    if (binary) {
        out << "b";
        out << displayed("%0b");
    } else {
        if (prefixed) out << "h";
        // Always deal with 4 bits at once.  Note no 4-state, it's above.
        out << displayed("%0h");
    }
    if (isNull() && VL_UNCOVERABLE(!isEqZero())) out << "-%E-null-not-zero";
    return out.str();
}

bool V3Number::displayedFmtLegal(char format, bool isScan) {
    // Is this a valid format letter?
    switch (tolower(format)) {
    case 'b': return true;
    case 'c': return true;
    case 'd': return true;  // Unsigned decimal
    case 'e': return true;
    case 'f': return true;
    case 'g': return true;
    case 'h': return true;
    case 'o': return true;
    case 'p': return true;  // Pattern
    case 's': return true;
    case 't': return true;
    case 'u': return true;  // Packed 2-state
    case 'v': return true;  // Strength
    case 'x': return true;
    case 'z': return true;  // Packed 4-state
    case '@': return true;  // Packed string
    case '~': return true;  // Signed decimal
    case '*': return isScan;  // $scan ignore argument
    default: return false;
    }
}

string V3Number::displayPad(size_t fmtsize, char pad, bool left, const string& in) {
    string padding;
    if (in.length() < fmtsize) padding = string(fmtsize - in.length(), pad);
    return left ? (in + padding) : (padding + in);
}

string V3Number::displayed(AstNode* nodep, const string& vformat) const {
    return displayed(nodep->fileline(), vformat);
}

string V3Number::displayed(FileLine* fl, const string& vformat) const {
    auto pos = vformat.cbegin();
    UASSERT(pos != vformat.cend() && pos[0] == '%',
            "$display-like function with non format argument " << *this);
    ++pos;
    bool left = false;
    if (pos[0] == '-') {
        left = true;
        ++pos;
    }
    string fmtsize;
    for (; pos != vformat.cend() && (isdigit(pos[0]) || pos[0] == '.'); ++pos) {
        fmtsize += pos[0];
    }
    string str;
    const char code = tolower(pos[0]);
    switch (code) {
    case 'b': {
        int bit = width() - 1;
        if (fmtsize == "0")
            while (bit && bitIs0(bit)) bit--;
        for (; bit >= 0; bit--) {
            if (bitIs0(bit)) {
                str += '0';
            } else if (bitIs1(bit)) {
                str += '1';
            } else if (bitIsZ(bit)) {
                str += 'z';
            } else {
                str += 'x';
            }
        }
        return str;
    }
    case 'o': {
        int bit = width() - 1;
        if (fmtsize == "0")
            while (bit && bitIs0(bit)) bit--;
        while ((bit % 3) != 2) bit++;
        for (; bit > 0; bit -= 3) {
            const int numX = countX(bit - 2, 3);
            const int numZ = countZ(bit - 2, 3);
            if (numX == 3 || numX == width() - (bit - 2)) {
                str += 'x';
                continue;
            }
            if (numZ == 3 || numZ == width() - (bit - 2)) {
                str += 'z';
                continue;
            }
            if (numX > 0) {
                str += 'X';
                continue;
            }
            if (numZ > 0) {
                str += 'Z';
                continue;
            }
            const int v = bitsValue(bit - 2, 3);
            str += static_cast<char>('0' + v);
        }
        return str;
    }
    case 'h':
    case 'x': {
        int bit = width() - 1;
        if (fmtsize == "0")
            while (bit && bitIs0(bit)) bit--;
        while ((bit % 4) != 3) bit++;
        for (; bit > 0; bit -= 4) {
            const int numX = countX(bit - 3, 4);
            const int numZ = countZ(bit - 3, 4);
            if (numX == 4 || numX == width() - (bit - 3)) {
                str += 'x';
                continue;
            }
            if (numZ == 4 || numZ == width() - (bit - 3)) {
                str += 'z';
                continue;
            }
            if (numX > 0) {
                str += 'X';
                continue;
            }
            if (numZ > 0) {
                str += 'Z';
                continue;
            }
            const int v = bitsValue(bit - 3, 4);
            if (v >= 10) {
                str += static_cast<char>('a' + v - 10);
            } else {
                str += static_cast<char>('0' + v);
            }
        }
        return str;
    }
    case 'c': {
        if (width() > 8) fl->v3warn(WIDTH, "$display-like format of %c format of > 8 bit value");
        const unsigned int v = bitsValue(0, 8);
        char strc[2];
        strc[0] = v & 0xff;
        strc[1] = '\0';
        str = strc;
        return str;
    }
    case 's': {
        // Spec says always drop leading zeros, this isn't quite right, we space pad.
        int bit = this->width() - 1;
        bool start = true;
        while ((bit % 8) != 7) bit++;
        for (; bit >= 0; bit -= 8) {
            const int v = bitsValue(bit - 7, 8);
            if (!start || v) {
                str += static_cast<char>((v == 0) ? ' ' : v);
                start = false;  // Drop leading 0s
            } else {
                if (fmtsize != "0") str += ' ';
            }
        }
        const size_t fmtsizen = static_cast<size_t>(atoi(fmtsize.c_str()));
        str = displayPad(fmtsizen, ' ', left, str);
        return str;
    }
    case '~':  // Signed decimal
    case 't':  // Time
    case 'd': {  // Unsigned decimal
        const bool issigned = (code == '~');
        if (fmtsize == "") {
            const double mantissabits = this->width() - (issigned ? 1 : 0);
            // To get the number of digits required, we want to compute
            // log10(2**mantissabits) and round it up. To be able to handle
            // a very wide mantissa, we use log2(2**mantissabits)/log2(10),
            // which is (+1.0 is for rounding bias):
            double dchars = mantissabits / 3.321928094887362 + 1.0;
            if (issigned) dchars++;  // space for sign
            fmtsize = cvtToStr(int(dchars));
        }
        bool hasXZ = false;
        if (isAllX()) {
            str = "x";
            hasXZ = true;
        } else if (isAllZ()) {
            str = "z";
            hasXZ = true;
        } else if (isAnyX()) {
            str = "X";
            hasXZ = true;
        } else if (isAnyZ()) {
            str = "Z";
            hasXZ = true;
        }
        if (!hasXZ) {
            if (issigned) {
                if (width() > 64) {
                    str = toDecimalS();
                } else {
                    str = cvtToStr(toSQuad());
                }
            } else {
                if (width() > 64) {
                    str = toDecimalU();
                } else {
                    str = cvtToStr(toUQuad());
                }
            }
        }
        const bool zeropad = fmtsize.length() > 0 && fmtsize[0] == '0';
        // fmtsize might have changed since we parsed the %fmtsize
        const size_t fmtsizen = static_cast<size_t>(atoi(fmtsize.c_str()));
        str = displayPad(fmtsizen, (zeropad ? '0' : ' '), left, str);
        return str;
    }
    case 'e':
    case 'f':
    case 'g':
    case '^': {  // Realtime
        char tmp[MAX_SPRINTF_DOUBLE_SIZE];
        VL_SNPRINTF(tmp, MAX_SPRINTF_DOUBLE_SIZE, vformat.c_str(), toDouble());
        return tmp;
    }
    // 'l'   // Library - converted to text by V3LinkResolve
    // 'p'   // Packed - converted to another code by V3Width
    case 'u': {  // Packed 2-state
        for (int i = 0; i < words(); i++) {
            const uint32_t v = m_value[i].m_value;
            str += static_cast<char>((v >> 0) & 0xff);
            str += static_cast<char>((v >> 8) & 0xff);
            str += static_cast<char>((v >> 16) & 0xff);
            str += static_cast<char>((v >> 24) & 0xff);
        }
        return str;
    }
    case 'z': {  // Packed 4-state
        for (int i = 0; i < words(); i++) {
            const ValueAndX v = m_value[i];
            str += static_cast<char>((v.m_value >> 0) & 0xff);
            str += static_cast<char>((v.m_value >> 8) & 0xff);
            str += static_cast<char>((v.m_value >> 16) & 0xff);
            str += static_cast<char>((v.m_value >> 24) & 0xff);
            str += static_cast<char>((v.m_valueX >> 0) & 0xff);
            str += static_cast<char>((v.m_valueX >> 8) & 0xff);
            str += static_cast<char>((v.m_valueX >> 16) & 0xff);
            str += static_cast<char>((v.m_valueX >> 24) & 0xff);
        }
        return str;
    }
    case 'v': {  // Strength
        int bit = width() - 1;
        for (; bit >= 0; bit--) {
            if (bitIs0(bit)) {
                str += "St0 ";
            }  // Yes, always a space even for bit 0
            else if (bitIs1(bit)) {
                str += "St1 ";
            } else if (bitIsZ(bit)) {
                str += "StZ ";
            } else {
                str += "StX";
            }
        }
        return str;
    }
    case '@': {  // Packed string
        const size_t fmtsizen = static_cast<size_t>(atoi(fmtsize.c_str()));
        str = displayPad(fmtsizen, ' ', left, toString());
        return str;
    }
    default:
        fl->v3fatalSrc("Unknown $display-like format code for number: %" << pos[0]);
        return "ERR";
    }
}

string V3Number::toDecimalS() const {
    if (isNegative()) {
        V3Number lhsNoSign = *this;
        lhsNoSign.opNegate(*this);
        return std::string{"-"} + lhsNoSign.toDecimalU();
    } else {
        return toDecimalU();
    }
}

string V3Number::toDecimalU() const {
    const int maxdecwidth = (width() + 3) * 4 / 3;

    // Or (maxdecwidth+7)/8], but can't have more than 4 BCD bits per word
    V3Number bcd(this, maxdecwidth + 4);
    V3Number tmp(this, maxdecwidth + 4);
    V3Number tmp2(this, maxdecwidth + 4);

    int from_bit = width() - 1;
    // Skip all leading zeros
    for (; from_bit >= 0 && bitIs0(from_bit); --from_bit) {}
    // Double-dabble algorithm
    for (; from_bit >= 0; --from_bit) {
        // Any digits >= 5 need an add 3 (via tmp)
        for (int nibble_bit = 0; nibble_bit < maxdecwidth; nibble_bit += 4) {
            if (bcd.bitsValue(nibble_bit, 4) >= 5) {
                tmp2.setAllBits0();
                tmp2.setBit(nibble_bit, 1);  // Add 3, decomposed as two bits
                tmp2.setBit(nibble_bit + 1, 1);
                tmp.opAssign(bcd);
                bcd.opAdd(tmp, tmp2);
            }
        }
        // Shift; bcd = bcd << 1
        tmp.opAssign(bcd);
        bcd.opShiftL(tmp, V3Number(this, 32, 1));
        // bcd[0] = this[from_bit]
        if (bitIs1(from_bit)) bcd.setBit(0, 1);
    }

    string output;
    int lsb = (maxdecwidth - 1) & ~3;
    for (; lsb > 0; lsb -= 4) {  // Skip leading zeros
        if (bcd.bitsValue(lsb, 4)) break;
    }
    for (; lsb >= 0; lsb -= 4) {
        output += static_cast<char>('0' + bcd.bitsValue(lsb, 4));  // 0..9
    }
    return output;
}

//======================================================================
// ACCESSORS - as numbers

uint32_t V3Number::toUInt() const {
    UASSERT(!isFourState(), "toUInt with 4-state " << *this);
    // We allow wide numbers that represent values <= 32 bits
    for (int i = 1; i < words(); ++i) {
        if (m_value[i].m_value) {
            v3error("Value too wide for 32-bits expected in this context " << *this);
            break;
        }
    }
    return m_value[0].m_value;
}

double V3Number::toDouble() const {
    if (VL_UNCOVERABLE(!isDouble() || width() != 64)) {
        v3fatalSrc("Real operation on wrong sized/non-real number");
    }
    union {
        double d;
        uint32_t u[2];
    } u;
    u.u[0] = m_value[0].m_value;
    u.u[1] = m_value[1].m_value;
    return u.d;
}

int32_t V3Number::toSInt() const {
    if (isSigned()) {
        const uint32_t v = toUInt();
        const uint32_t signExtend = (-(v & (1UL << (width() - 1))));
        const uint32_t extended = v | signExtend;
        return static_cast<int32_t>(extended);
    } else {
        // Where we use this (widths, etc) and care about signedness,
        // we can reasonably assume the MSB isn't set on unsigned numbers.
        return static_cast<int32_t>(toUInt());
    }
}

uint64_t V3Number::toUQuad() const {
    UASSERT(!isFourState(), "toUQuad with 4-state " << *this);
    // We allow wide numbers that represent values <= 64 bits
    if (isDouble()) return static_cast<uint64_t>(toDouble());
    for (int i = 2; i < words(); ++i) {
        if (m_value[i].m_value) {
            v3error("Value too wide for 64-bits expected in this context " << *this);
            break;
        }
    }
    if (width() <= 32) return (static_cast<uint64_t>(toUInt()));
    return ((static_cast<uint64_t>(m_value[1].m_value) << 32ULL)
            | (static_cast<uint64_t>(m_value[0].m_value)));
}

int64_t V3Number::toSQuad() const {
    if (isDouble()) return static_cast<int64_t>(toDouble());
    const uint64_t v = toUQuad();
    const uint64_t signExtend = (-(v & (1ULL << (width() - 1))));
    const uint64_t extended = v | signExtend;
    return static_cast<int64_t>(extended);
}

string V3Number::toString() const {
    UASSERT(!isFourState(), "toString with 4-state " << *this);
    // Spec says always drop leading zeros, this isn't quite right, we space pad.
    if (isString()) return m_stringVal;
    int bit = this->width() - 1;
    bool start = true;
    while ((bit % 8) != 7) bit++;
    string str;
    for (; bit >= 0; bit -= 8) {
        const int v = bitsValue(bit - 7, 8);
        if (!start || v) {
            str += static_cast<char>((v == 0) ? ' ' : v);
            start = false;  // Drop leading 0s
        }
    }
    return str;
}

V3Hash V3Number::toHash() const {
    V3Hash hash(m_width);
    for (int i = 0; i < words(); ++i) { hash += m_value[i].m_value; }
    return hash;
}

uint32_t V3Number::edataWord(int eword) const {
    UASSERT(!isFourState(), "edataWord with 4-state " << *this);
    return m_value[eword].m_value;
}

uint8_t V3Number::dataByte(int byte) const {
    return (edataWord(byte / (VL_EDATASIZE / 8)) >> ((byte * 8) % VL_EDATASIZE)) & 0xff;
}

bool V3Number::isAllZ() const {
    for (int i = 0; i < width(); i++) {
        if (!bitIsZ(i)) return false;
    }
    return true;
}
bool V3Number::isAllX() const {
    uint32_t mask = hiWordMask();
    for (int i = words() - 1; i >= 0; --i) {
        const ValueAndX v = m_value[i];
        if ((v.m_value & v.m_valueX) ^ mask) return false;
        mask = ~0U;
    }
    return true;
}
bool V3Number::isEqZero() const {
    for (int i = 0; i < words(); i++) {
        const ValueAndX v = m_value[i];
        if (v.m_value || v.m_valueX) return false;
    }
    return true;
}
bool V3Number::isNeqZero() const {
    for (int i = 0; i < words(); i++) {
        const ValueAndX v = m_value[i];
        if (v.m_value & ~v.m_valueX) return true;
    }
    return false;
}
bool V3Number::isBitsZero(int msb, int lsb) const {
    for (int i = lsb; i <= msb; i++) {
        if (VL_UNLIKELY(!bitIs0(i))) return false;
    }
    return true;
}
bool V3Number::isEqOne() const {
    if (m_value[0].m_value != 1 || m_value[0].m_valueX) return false;
    for (int i = 1; i < words(); i++) {
        const ValueAndX v = m_value[i];
        if (v.m_value || v.m_valueX) return false;
    }
    return true;
}
bool V3Number::isEqAllOnes(int optwidth) const {
    if (!optwidth) optwidth = width();
    for (int bit = 0; bit < optwidth; bit++) {
        if (!bitIs1(bit)) return false;
    }
    return true;
}
bool V3Number::isFourState() const {
    if (isDouble() || isString()) return false;
    for (int i = 0; i < words(); ++i) {
        if (m_value[i].m_valueX) return true;
    }
    return false;
}
bool V3Number::isAnyX() const {
    if (isDouble() || isString()) return false;
    for (int bit = 0; bit < width(); bit++) {
        if (bitIsX(bit)) return true;
    }
    return false;
}
bool V3Number::isAnyXZ() const { return isAnyX() || isAnyZ(); }
bool V3Number::isAnyZ() const {
    if (isDouble() || isString()) return false;
    for (int bit = 0; bit < width(); bit++) {
        if (bitIsZ(bit)) return true;
    }
    return false;
}
bool V3Number::isLtXZ(const V3Number& rhs) const {
    // Include X/Z in comparisons for sort ordering
    for (int bit = 0; bit < std::max(this->width(), rhs.width()); bit++) {
        if (this->bitIs1(bit) && rhs.bitIs0(bit)) return true;
        if (rhs.bitIs1(bit) && this->bitIs0(bit)) return false;
        if (this->bitIsXZ(bit)) return true;
        if (rhs.bitIsXZ(bit)) return false;
    }
    return false;
}
int V3Number::countX(int lsb, int nbits) const {
    int count = 0;
    for (int bitn = 0; bitn < nbits; ++bitn) {
        if (lsb + bitn >= width()) return count;
        if (bitIsX(lsb + bitn)) ++count;
    }
    return count;
}
int V3Number::countZ(int lsb, int nbits) const {
    int count = 0;
    for (int bitn = 0; bitn < nbits; ++bitn) {
        if (lsb + bitn >= width()) return count;
        if (bitIsZ(lsb + bitn)) ++count;
    }
    return count;
}

int V3Number::widthMin() const {
    for (int bit = width() - 1; bit > 0; bit--) {
        if (!bitIs0(bit)) return bit + 1;
    }
    return 1;  // one bit even if number is == 0
}

uint32_t V3Number::countBits(const V3Number& ctrl) const {
    int n = 0;
    for (int bit = 0; bit < this->width(); ++bit) {
        switch (ctrl.bitIs(0)) {
        case '0':
            if (bitIs0(bit)) ++n;
            break;
        case '1':
            if (bitIs1(bit)) ++n;
            break;
        case 'x':
            if (bitIsX(bit)) ++n;
            break;
        case 'z':
            if (bitIsZ(bit)) ++n;
            break;
        }
    }
    return n;
}

uint32_t V3Number::countBits(const V3Number& ctrl1, const V3Number& ctrl2,
                             const V3Number& ctrl3) const {
    int n = countBits(ctrl1);
    if (ctrl2.bitIs(0) != ctrl1.bitIs(0)) n += countBits(ctrl2);
    if ((ctrl3.bitIs(0) != ctrl1.bitIs(0)) && (ctrl3.bitIs(0) != ctrl2.bitIs(0))) {
        n += countBits(ctrl3);
    }
    return n;
}

uint32_t V3Number::countOnes() const {
    int n = 0;
    for (int bit = 0; bit < this->width(); bit++) {
        if (bitIs1(bit)) n++;
    }
    return n;
}

uint32_t V3Number::mostSetBitP1() const {
    for (int bit = this->width() - 1; bit >= 0; bit--) {
        if (bitIs1(bit)) return bit + 1;
    }
    return 0;
}
//======================================================================

V3Number& V3Number::opBitsNonX(const V3Number& lhs) {  // 0/1->1, X/Z->0
    // op i, L(lhs) bit return
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    setZero();
    for (int bit = 0; bit < this->width(); bit++) {
        if (lhs.bitIs0(bit) || lhs.bitIs1(bit)) setBit(bit, 1);
    }
    return *this;
}
V3Number& V3Number::opBitsOne(const V3Number& lhs) {  // 1->1, 0/X/Z->0
    // op i, L(lhs) bit return
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    setZero();
    for (int bit = 0; bit < this->width(); bit++) {
        if (lhs.bitIs1(bit)) setBit(bit, 1);
    }
    return *this;
}
V3Number& V3Number::opBitsXZ(const V3Number& lhs) {  // 0/1->1, X/Z->0
    // op i, L(lhs) bit return
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    setZero();
    for (int bit = 0; bit < this->width(); bit++) {
        if (lhs.bitIsXZ(bit)) setBit(bit, 1);
    }
    return *this;
}
V3Number& V3Number::opBitsZ(const V3Number& lhs) {  // 0/1->1, X/Z->0
    // op i, L(lhs) bit return
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    setZero();
    for (int bit = 0; bit < this->width(); bit++) {
        if (lhs.bitIsZ(bit)) setBit(bit, 1);
    }
    return *this;
}
V3Number& V3Number::opBitsNonZ(const V3Number& lhs) {  // 0/1->1, X/Z->0
    // op i, L(lhs) bit return
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    setZero();
    for (int bit = 0; bit < this->width(); bit++) {
        if (!lhs.bitIsZ(bit)) setBit(bit, 1);
    }
    return *this;
}

//======================================================================
// Operators - Simple per-bit logical ops

V3Number& V3Number::opRedOr(const V3Number& lhs) {
    // op i, 1 bit return
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    char outc = 0;
    for (int bit = 0; bit < lhs.width(); bit++) {
        if (lhs.bitIs1(bit)) {
            return setSingleBits(1);
        } else if (lhs.bitIs0(bit)) {
        } else {
            outc = 'x';
        }
    }
    return setSingleBits(outc);
}

V3Number& V3Number::opRedAnd(const V3Number& lhs) {
    // op i, 1 bit return
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    char outc = 1;
    for (int bit = 0; bit < lhs.width(); bit++) {
        if (lhs.bitIs0(bit)) {
            return setSingleBits(0);
        } else if (lhs.bitIs1(bit)) {
        } else {
            outc = 'x';
        }
    }
    return setSingleBits(outc);
}

V3Number& V3Number::opRedXor(const V3Number& lhs) {
    // op i, 1 bit return
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    char outc = 0;
    for (int bit = 0; bit < lhs.width(); bit++) {
        if (lhs.bitIs1(bit)) {
            if (outc == 1) {
                outc = 0;
            } else if (outc == 0) {
                outc = 1;
            }
        } else if (lhs.bitIs0(bit)) {
        } else {
            outc = 'x';
        }
    }
    return setSingleBits(outc);
}

V3Number& V3Number::opCountBits(const V3Number& expr, const V3Number& ctrl1, const V3Number& ctrl2,
                                const V3Number& ctrl3) {
    NUM_ASSERT_OP_ARGS4(expr, ctrl1, ctrl2, ctrl3);
    NUM_ASSERT_LOGIC_ARGS4(expr, ctrl1, ctrl2, ctrl3);
    setZero();
    m_value[0].m_value = expr.countBits(ctrl1, ctrl2, ctrl3);
    opCleanThis();
    return *this;
}
V3Number& V3Number::opCountOnes(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    if (lhs.isFourState()) return setAllBitsX();
    setZero();
    m_value[0].m_value = lhs.countOnes();
    opCleanThis();
    return *this;
}
V3Number& V3Number::opIsUnknown(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    return setSingleBits(lhs.isAnyXZ());
}
V3Number& V3Number::opOneHot(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    if (lhs.isFourState()) return setAllBitsX();
    return setSingleBits(lhs.countOnes() == 1);
}
V3Number& V3Number::opOneHot0(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    if (lhs.isFourState()) return setAllBitsX();
    return setSingleBits(lhs.countOnes() <= 1);
}
V3Number& V3Number::opCLog2(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    if (lhs.isFourState()) return setAllBitsX();
    // IE if 4, this algorithm didn't pre-subtract 1, so we need to post-correct now
    const int adjust = (lhs.countOnes() == 1) ? 0 : 1;
    for (int bit = lhs.width() - 1; bit >= 0; bit--) {
        if (lhs.bitIs1(bit)) {
            setLong(bit + adjust);
            return *this;
        }
    }
    setZero();
    return *this;
}

V3Number& V3Number::opLogNot(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    // op i, 1 bit return
    char outc = 1;
    for (int bit = 0; bit < lhs.width(); bit++) {
        if (lhs.bitIs1(bit)) {
            outc = 0;
            goto last;
        } else if (lhs.bitIs0(bit)) {
        } else {
            outc = 'x';
        }
    }
last:
    return setSingleBits(outc);
}

V3Number& V3Number::opNot(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    // op i, L(lhs) bit return
    setZero();
    for (int bit = 0; bit < this->width(); bit++) {
        if (lhs.bitIs0(bit)) {
            setBit(bit, 1);
        } else if (lhs.bitIsXZ(bit)) {
            setBit(bit, 'x');
        }
    }
    return *this;
}

V3Number& V3Number::opAnd(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    // i op j, max(L(lhs),L(rhs)) bit return, careful need to X/Z extend.
    setZero();
    for (int bit = 0; bit < this->width(); bit++) {
        if (lhs.bitIs1(bit) && rhs.bitIs1(bit)) {
            setBit(bit, 1);
        } else if (lhs.bitIs0(bit) || rhs.bitIs0(bit)) {  // 0
        } else {
            setBit(bit, 'x');
        }
    }
    return *this;
}

V3Number& V3Number::opOr(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    // i op j, max(L(lhs),L(rhs)) bit return, careful need to X/Z extend.
    setZero();
    for (int bit = 0; bit < this->width(); bit++) {
        if (lhs.bitIs1(bit) || rhs.bitIs1(bit)) {
            setBit(bit, 1);
        } else if (lhs.bitIs0(bit) && rhs.bitIs0(bit)) {
            // 0
        } else {
            setBit(bit, 'x');
        }
    }
    return *this;
}

V3Number& V3Number::opXor(const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, careful need to X/Z extend.
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    setZero();
    for (int bit = 0; bit < this->width(); bit++) {
        if (lhs.bitIs1(bit) && rhs.bitIs0(bit)) {
            setBit(bit, 1);
        } else if (lhs.bitIs0(bit) && rhs.bitIs1(bit)) {
            setBit(bit, 1);
        } else if (lhs.bitIsXZ(bit) || rhs.bitIsXZ(bit)) {
            setBit(bit, 'x');
        }
        // else zero
    }
    return *this;
}

V3Number& V3Number::opConcat(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    setZero();
    // See also error in V3Width
    if (!lhs.sized() || !rhs.sized()) {
        v3warn(WIDTHCONCAT, "Unsized numbers/parameters not allowed in concatenations.");
    }
    int obit = 0;
    for (int bit = 0; bit < rhs.width(); bit++) {
        setBit(obit, rhs.bitIs(bit));
        obit++;
    }
    for (int bit = 0; bit < lhs.width(); bit++) {
        setBit(obit, lhs.bitIs(bit));
        obit++;
    }
    return *this;
}

V3Number& V3Number::opLenN(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_STRING_ARGS1(lhs);
    setQuad(lhs.toString().length());
    return *this;
}

V3Number& V3Number::opRepl(const V3Number& lhs,
                           const V3Number& rhs) {  // rhs is # of times to replicate
    // Hopefully the using routine has a error check to, &rhso.
    // See also error in V3Width
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    if (!lhs.sized()) {
        v3warn(WIDTHCONCAT, "Unsized numbers/parameters not allowed in replications.");
    }
    return opRepl(lhs, rhs.toUInt());
}

V3Number& V3Number::opRepl(const V3Number& lhs,
                           uint32_t rhsval) {  // rhs is # of times to replicate
    // i op repl, L(i)*value(rhs) bit return
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    setZero();
    if (rhsval > 8192) {
        v3warn(WIDTHCONCAT, "More than a 8k bit replication is probably wrong: " << rhsval);
    }
    int obit = 0;
    for (unsigned times = 0; times < rhsval; times++) {
        for (int bit = 0; bit < lhs.width(); bit++) {
            setBit(obit, lhs.bitIs(bit));
            obit++;
        }
    }
    return *this;
}

V3Number& V3Number::opStreamL(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    setZero();
    // See also error in V3Width
    if (!lhs.sized()) {
        v3warn(WIDTHCONCAT, "Unsized numbers/parameters not allowed in streams.");
    }
    // Slice size should never exceed the lhs width
    const int ssize = std::min(rhs.toUInt(), static_cast<unsigned>(lhs.width()));
    for (int istart = 0; istart < lhs.width(); istart += ssize) {
        const int ostart = std::max(0, lhs.width() - ssize - istart);
        for (int bit = 0; bit < ssize && bit < lhs.width() - istart; bit++) {
            setBit(ostart + bit, lhs.bitIs(istart + bit));
        }
    }
    return *this;
}

V3Number& V3Number::opLogAnd(const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    char loutc = 0;
    char routc = 0;
    for (int bit = 0; bit < lhs.width(); bit++) {
        if (lhs.bitIs1(bit)) {
            loutc = 1;
            break;
        }
        if (lhs.bitIsXZ(bit) && loutc == 0) loutc = 'x';
    }
    for (int bit = 0; bit < rhs.width(); bit++) {
        if (rhs.bitIs1(bit)) {
            routc = 1;
            break;
        }
        if (rhs.bitIsXZ(bit) && routc == 0) routc = 'x';
    }
    char outc = 'x';
    if (routc == 1 && loutc == 1) outc = 1;
    if (routc == 0 || loutc == 0) outc = 0;
    return setSingleBits(outc);
}

V3Number& V3Number::opLogOr(const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    char outc = 0;
    for (int bit = 0; bit < lhs.width(); bit++) {
        if (lhs.bitIs1(bit)) {
            outc = 1;
            goto last;
        }
        if (lhs.bitIsXZ(bit) && outc == 0) outc = 'x';
    }
    for (int bit = 0; bit < rhs.width(); bit++) {
        if (rhs.bitIs1(bit)) {
            outc = 1;
            goto last;
        }
        if (rhs.bitIsXZ(bit) && outc == 0) outc = 'x';
    }
last:
    return setSingleBits(outc);
}

V3Number& V3Number::opLogIf(const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to
    // X/Z extend. Use definition in IEEE to do this for us.
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    V3Number lnot = lhs;
    lnot.opLogNot(lhs);
    return opLogOr(lnot, rhs);
}

V3Number& V3Number::opLogEq(const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to
    // X/Z extend. Use definition in IEEE to do this for us.
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    V3Number ifa = lhs;
    ifa.opLogIf(lhs, rhs);
    V3Number ifb = rhs;
    ifb.opLogIf(rhs, lhs);
    return opLogAnd(ifa, ifb);
}

V3Number& V3Number::opAtoN(const V3Number& lhs, int base) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_STRING_ARGS1(lhs);
    UASSERT(base == AstAtoN::ATOREAL || base == 2 || base == 8 || base == 10 || base == 16,
            "base must be one of AstAtoN::ATOREAL, 2, 8, 10, or 16.");

    std::string str = lhs.toString();  // new instance to edit later
    if (base == AstAtoN::ATOREAL) return setDouble(std::atof(str.c_str()));

    // IEEE 1800-2017 6.16.9 says '_' may exist.
    str.erase(std::remove(str.begin(), str.end(), '_'), str.end());

    errno = 0;
    auto v = std::strtol(str.c_str(), nullptr, base);
    if (errno != 0) v = 0;
    return setLongS(static_cast<int32_t>(v));
}

V3Number& V3Number::opPutcN(const V3Number& lhs, const V3Number& rhs, const V3Number& ths) {
    NUM_ASSERT_OP_ARGS3(lhs, rhs, ths);
    NUM_ASSERT_STRING_ARGS1(lhs);
    string lstring = lhs.toString();
    const int32_t i = rhs.toSInt();
    const int32_t c = ths.toSInt() & 0xFF;
    // 6.16.2:str.putc(i, c) does not change the value when i < 0 || i >= str.len() || c == 0
    // when evaluating the second condition, i must be positive.
    if (0 <= i && static_cast<uint32_t>(i) < lstring.length() && c != 0) lstring[i] = c;
    return setString(lstring);
}

V3Number& V3Number::opGetcN(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_STRING_ARGS1(lhs);
    const string lstring = lhs.toString();
    const int32_t i = rhs.toSInt();
    int32_t v = 0;
    // 6.16.3:str.getc(i) returns 0 if i < 0 || i >= str.len()
    // when evaluating the second condition, i must be positive.
    if (0 <= i && static_cast<uint32_t>(i) < lstring.length()) v = lstring[i];
    return setLong(v);
}

V3Number& V3Number::opSubstrN(const V3Number& lhs, const V3Number& rhs, const V3Number& ths) {
    NUM_ASSERT_OP_ARGS3(lhs, rhs, ths);
    NUM_ASSERT_STRING_ARGS1(lhs);
    const string lstring = lhs.toString();
    const int32_t i = rhs.toSInt();
    const int32_t j = ths.toSInt();
    // 6.16.8:str.substr(i, j) returns an empty string when i < 0 || j < i || j >= str.len()
    // when evaluating the third condition, j must be positive because 0 <= i <= j is guaranteed by
    // the former two conditions.
    if (i < 0 || j < i || static_cast<uint32_t>(j) >= lstring.length()) return setString("");
    // The second parameter of std::string::substr(i, n) is length, not position as SystemVerilog.
    return setString(lstring.substr(i, j - i + 1));
}

V3Number& V3Number::opCompareNN(const V3Number& lhs, const V3Number& rhs, bool ignoreCase) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_STRING_ARGS2(lhs, rhs);
    // SystemVerilog Language Standard does not allow a string variable to contain '\0'.
    // So C functions such as strcmp() can correctly compare strings.
    int result;
    const string lstring = lhs.toString();
    const string rstring = rhs.toString();
    if (ignoreCase) {
        result = VL_STRCASECMP(lstring.c_str(), rstring.c_str());
    } else {
        result = std::strcmp(lstring.c_str(), rstring.c_str());
    }
    return setLongS(result);
}

V3Number& V3Number::opEq(const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    if (lhs.isString()) return opEqN(lhs, rhs);
    if (lhs.isDouble()) return opEqD(lhs, rhs);
    char outc = 1;
    for (int bit = 0; bit < std::max(lhs.width(), rhs.width()); bit++) {
        if (lhs.bitIs1(bit) && rhs.bitIs0(bit)) {
            outc = 0;
            goto last;
        }
        if (lhs.bitIs0(bit) && rhs.bitIs1(bit)) {
            outc = 0;
            goto last;
        }
        if (lhs.bitIsXZ(bit)) outc = 'x';
        if (rhs.bitIsXZ(bit)) outc = 'x';
    }
last:
    return setSingleBits(outc);
}

V3Number& V3Number::opNeq(const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    if (lhs.isString()) return opNeqN(lhs, rhs);
    if (lhs.isDouble()) return opNeqD(lhs, rhs);
    char outc = 0;
    for (int bit = 0; bit < std::max(lhs.width(), rhs.width()); bit++) {
        if (lhs.bitIs1(bit) && rhs.bitIs0(bit)) {
            outc = 1;
            goto last;
        }
        if (lhs.bitIs0(bit) && rhs.bitIs1(bit)) {
            outc = 1;
            goto last;
        }
        if (lhs.bitIsXZ(bit)) outc = 'x';
        if (rhs.bitIsXZ(bit)) outc = 'x';
    }
last:
    return setSingleBits(outc);
}

bool V3Number::isCaseEq(const V3Number& rhs) const {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    if (isString()) return toString() == rhs.toString();
    if (isDouble()) return toDouble() == rhs.toDouble();
    if (this->width() != rhs.width()) return false;
    for (int i = 0; i < words(); ++i) {
        if (!(m_value[i] == rhs.m_value[i])) return false;
    }
    return true;
}

V3Number& V3Number::opCaseEq(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    return setSingleBits(lhs.isCaseEq(rhs) ? 1 : 0);
}

V3Number& V3Number::opCaseNeq(const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    char outc = 0;
    if (lhs.isString()) {
        return opNeqN(lhs, rhs);
    } else if (lhs.isDouble()) {
        return opNeqD(lhs, rhs);
    }
    for (int bit = 0; bit < std::max(lhs.width(), rhs.width()); bit++) {
        if (lhs.bitIs(bit) != rhs.bitIs(bit)) {
            outc = 1;
            goto last;
        }
    }
last:
    return setSingleBits(outc);
}

V3Number& V3Number::opWildEq(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    char outc = 1;
    for (int bit = 0; bit < std::max(lhs.width(), rhs.width()); bit++) {
        if (!rhs.bitIsXZ(bit) && lhs.bitIs(bit) != rhs.bitIs(bit)) {
            outc = 0;
            goto last;
        }
        if (lhs.bitIsXZ(bit)) outc = 'x';
    }
last:
    return setSingleBits(outc);
}

V3Number& V3Number::opWildNeq(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    char outc = 0;
    for (int bit = 0; bit < std::max(lhs.width(), rhs.width()); bit++) {
        if (!rhs.bitIsXZ(bit) && lhs.bitIs(bit) != rhs.bitIs(bit)) {
            outc = 1;
            goto last;
        }
        if (lhs.bitIsXZ(bit)) outc = 'x';
    }
last:
    return setSingleBits(outc);
}

V3Number& V3Number::opGt(const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    char outc = 0;
    for (int bit = 0; bit < std::max(lhs.width(), rhs.width()); bit++) {
        if (lhs.bitIs1(bit) && rhs.bitIs0(bit)) outc = 1;
        if (rhs.bitIs1(bit) && lhs.bitIs0(bit)) outc = 0;
        if (lhs.bitIsXZ(bit)) outc = 'x';
        if (rhs.bitIsXZ(bit)) outc = 'x';
    }
    return setSingleBits(outc);
}

V3Number& V3Number::opGtS(const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    char outc = 0;
    {
        const int mbit = std::max(lhs.width() - 1, rhs.width() - 1);
        if (lhs.bitIsXZ(mbit)) {
            outc = 'x';
        } else if (rhs.bitIsXZ(mbit)) {
            outc = 'x';
        } else if (lhs.bitIs0(mbit) && rhs.bitIs1Extend(mbit)) {
            outc = 1;  // + > -
        } else if (lhs.bitIs1Extend(mbit) && rhs.bitIs0(mbit)) {
            outc = 0;  // - !> +
        } else {
            // both positive or negative, normal >
            for (int bit = 0; bit < std::max(lhs.width() - 1, rhs.width() - 1); bit++) {
                if (lhs.bitIs1Extend(bit) && rhs.bitIs0(bit)) outc = 1;
                if (rhs.bitIs1Extend(bit) && lhs.bitIs0(bit)) outc = 0;
                if (lhs.bitIsXZ(bit)) outc = 'x';
                if (rhs.bitIsXZ(bit)) outc = 'x';
            }
        }
    }
    return setSingleBits(outc);
}

V3Number& V3Number::opGte(const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    V3Number& eq = opEq(lhs, rhs);
    if (eq.isNeqZero()) return eq;  // Return true
    return opGt(lhs, rhs);
}

V3Number& V3Number::opGteS(const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    V3Number& eq = opEq(lhs, rhs);
    if (eq.isNeqZero()) return eq;  // Return true
    return opGtS(lhs, rhs);
}

V3Number& V3Number::opLt(const V3Number& lhs, const V3Number& rhs) { return opGt(rhs, lhs); }
V3Number& V3Number::opLte(const V3Number& lhs, const V3Number& rhs) { return opGte(rhs, lhs); }
V3Number& V3Number::opLtS(const V3Number& lhs, const V3Number& rhs) { return opGtS(rhs, lhs); }
V3Number& V3Number::opLteS(const V3Number& lhs, const V3Number& rhs) { return opGteS(rhs, lhs); }

V3Number& V3Number::opShiftR(const V3Number& lhs, const V3Number& rhs) {
    // L(lhs) bit return
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    if (rhs.isFourState()) return setAllBitsX();
    setZero();
    for (int bit = 32; bit < rhs.width(); bit++) {
        if (rhs.bitIs1(bit)) return *this;  // shift of over 2^32 must be zero
    }
    const uint32_t rhsval = rhs.toUInt();
    if (rhsval < static_cast<uint32_t>(lhs.width())) {
        for (int bit = 0; bit < this->width(); bit++) setBit(bit, lhs.bitIs(bit + rhsval));
    }
    return *this;
}

V3Number& V3Number::opShiftRS(const V3Number& lhs, const V3Number& rhs, uint32_t lbits) {
    // L(lhs) bit return
    // The spec says a unsigned >>> still acts as a normal >>.
    // We presume it is signed; as that's V3Width's job to convert to opShiftR
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    if (rhs.isFourState()) return setAllBitsX();
    setZero();
    for (int bit = 32; bit < rhs.width(); bit++) {
        for (int sbit = 0; sbit < this->width(); sbit++) {
            setBit(sbit, lhs.bitIs(lbits - 1));  // 0/1/X/Z
        }
        if (rhs.bitIs1(lbits - 1)) setAllBits1();  // -1 else 0
        return *this;  // shift of over 2^32 must be -1/0
    }
    const uint32_t rhsval = rhs.toUInt();
    if (rhsval < static_cast<uint32_t>(lhs.width())) {
        for (int bit = 0; bit < this->width(); bit++) {
            setBit(bit, lhs.bitIsExtend(bit + rhsval, lbits));
        }
    } else {
        for (int bit = 0; bit < this->width(); bit++) {
            setBit(bit, lhs.bitIs(lbits - 1));  // 0/1/X/Z
        }
    }
    return *this;
}

V3Number& V3Number::opShiftL(const V3Number& lhs, const V3Number& rhs) {
    // L(lhs) bit return
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    if (rhs.isFourState()) return setAllBitsX();
    setZero();
    for (int bit = 32; bit < rhs.width(); bit++) {
        if (rhs.bitIs1(bit)) return *this;  // shift of over 2^32 must be zero
    }
    const uint32_t rhsval = rhs.toUInt();
    for (int bit = 0; bit < this->width(); bit++) {
        if (bit >= static_cast<int>(rhsval)) setBit(bit, lhs.bitIs(bit - rhsval));
    }
    return *this;
}

//======================================================================
// Ops - Arithmetic

V3Number& V3Number::opNegate(const V3Number& lhs) {
    // op i, L(lhs) bit return
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    if (lhs.isFourState()) return setAllBitsX();
    V3Number notlhs(&lhs, width());
    notlhs.opNot(lhs);
    const V3Number one(&lhs, width(), 1);
    opAdd(notlhs, one);
    return *this;
}
V3Number& V3Number::opAdd(const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, if any 4-state, 4-state return
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    setZero();
    // Addem
    int carry = 0;
    for (int bit = 0; bit < this->width(); bit++) {
        const int sum = ((lhs.bitIs1(bit) ? 1 : 0) + (rhs.bitIs1(bit) ? 1 : 0) + carry);
        if (sum & 1) setBit(bit, 1);
        carry = (sum >= 2);
    }
    return *this;
}
V3Number& V3Number::opSub(const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, if any 4-state, 4-state return
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    V3Number negrhs(&rhs, rhs.width());
    negrhs.opNegate(rhs);
    return opAdd(lhs, negrhs);
}
V3Number& V3Number::opMul(const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, if any 4-state, 4-state return
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    setZero();
    if (width() <= 64) {
        setQuad(lhs.toUQuad() * rhs.toUQuad());
        opCleanThis();  // Mult produces extra bits in result
    } else {
        for (int lword = 0; lword < lhs.words(); lword++) {
            const uint64_t lwordval = static_cast<uint64_t>(lhs.m_value[lword].m_value);
            if (lwordval == 0) continue;
            for (int rword = 0; rword < rhs.words(); rword++) {
                const uint64_t rwordval = static_cast<uint64_t>(rhs.m_value[rword].m_value);
                if (rwordval == 0) continue;
                uint64_t mul = lwordval * rwordval;
                for (int qword = lword + rword; qword < this->words(); qword++) {
                    mul += static_cast<uint64_t>(m_value[qword].m_value);
                    m_value[qword].m_value = (mul & 0xffffffffULL);
                    mul = (mul >> 32ULL) & 0xffffffffULL;
                    if (mul == 0) break;
                }
            }
        }
        opCleanThis();  // Mult produces extra bits in result
    }
    return *this;
}
V3Number& V3Number::opMulS(const V3Number& lhs, const V3Number& rhs) {
    // Signed multiply
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    V3Number lhsNoSign = lhs;
    if (lhs.isNegative()) lhsNoSign.opNegate(lhs);
    V3Number rhsNoSign = rhs;
    if (rhs.isNegative()) rhsNoSign.opNegate(rhs);
    const V3Number qNoSign = opMul(lhsNoSign, rhsNoSign);
    if ((lhs.isNegative() && !rhs.isNegative()) || (!lhs.isNegative() && rhs.isNegative())) {
        opNegate(qNoSign);
    } else {
        opAssign(qNoSign);
    }
    return *this;
}
V3Number& V3Number::opDiv(const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, if any 4-state, 4-state return
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    // UINFO(9, "opdiv "<<lhs<<" "<<rhs<<endl);
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    if (rhs.isEqZero()) return setAllBitsXRemoved();
    if (lhs.width() <= 64) {
        setQuad(lhs.toUQuad() / rhs.toUQuad());
        return *this;
    } else {
        // Wide division
        return opModDivGuts(lhs, rhs, false);
    }
}
V3Number& V3Number::opDivS(const V3Number& lhs, const V3Number& rhs) {
    // Signed divide
    // UINFO(9, ">>divs-start "<<lhs<<" "<<rhs<<endl);
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    if (rhs.isEqZero()) return setAllBitsXRemoved();
    V3Number lhsNoSign = lhs;
    if (lhs.isNegative()) lhsNoSign.opNegate(lhs);
    V3Number rhsNoSign = rhs;
    if (rhs.isNegative()) rhsNoSign.opNegate(rhs);
    const V3Number qNoSign = opDiv(lhsNoSign, rhsNoSign);
    // UINFO(9, " >divs-mid "<<lhs<<" "<<rhs<<" "<<qNoSign<<endl);
    if ((lhs.isNegative() && !rhs.isNegative()) || (!lhs.isNegative() && rhs.isNegative())) {
        opNegate(qNoSign);
    } else {
        opAssign(qNoSign);
    }
    UINFO(9, " <divs-out " << lhs << " " << rhs << " =" << *this << endl);
    return *this;
}
V3Number& V3Number::opModDiv(const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, if any 4-state, 4-state return
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    if (rhs.isEqZero()) return setAllBitsXRemoved();
    if (lhs.width() <= 64) {
        setQuad(lhs.toUQuad() % rhs.toUQuad());
        return *this;
    } else {
        // Wide modulus
        return opModDivGuts(lhs, rhs, true);
    }
}
V3Number& V3Number::opModDivS(const V3Number& lhs, const V3Number& rhs) {
    // Signed moddiv
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    if (rhs.isEqZero()) return setAllBitsXRemoved();
    V3Number lhsNoSign = lhs;
    if (lhs.isNegative()) lhsNoSign.opNegate(lhs);
    V3Number rhsNoSign = rhs;
    if (rhs.isNegative()) rhsNoSign.opNegate(rhs);
    const V3Number qNoSign = opModDiv(lhsNoSign, rhsNoSign);
    if (lhs.isNegative()) {  // Just lhs' sign  (*DIFFERENT FROM PERL, which uses rhs sign*)
        opNegate(qNoSign);
    } else {
        opAssign(qNoSign);
    }
    return *this;
}
V3Number& V3Number::opModDivGuts(const V3Number& lhs, const V3Number& rhs, bool is_modulus) {
    // See Knuth Algorithm D.  Computes u/v = q.r
    // This isn't massively tuned, as wide division is rare
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    setZero();
    // Find MSB and check for zero.
    const int words = lhs.words();
    const int umsbp1 = lhs.mostSetBitP1();  // dividend
    const int vmsbp1 = rhs.mostSetBitP1();  // divisor
    if (VL_UNLIKELY(vmsbp1 == 0)  // rwp==0 so division by zero.  Return 0.
        || VL_UNLIKELY(umsbp1 == 0)) {  // 0/x so short circuit and return 0
        UINFO(9, "  opmoddiv-zero " << lhs << " " << rhs << " now=" << *this << endl);
        return *this;
    }

    const int uw = (umsbp1 + 31) / 32;  // aka "m" in the algorithm
    const int vw = (vmsbp1 + 31) / 32;  // aka "n" in the algorithm

    if (vw == 1) {  // Single divisor word breaks rest of algorithm
        uint64_t k = 0;
        for (int j = uw - 1; j >= 0; j--) {
            const uint64_t unw64 = ((k << 32ULL) + static_cast<uint64_t>(lhs.m_value[j].m_value));
            m_value[j].m_value = unw64 / static_cast<uint64_t>(rhs.m_value[0].m_value);
            k = unw64
                - (static_cast<uint64_t>(m_value[j].m_value)
                   * static_cast<uint64_t>(rhs.m_value[0].m_value));
        }
        UINFO(9, "  opmoddiv-1w  " << lhs << " " << rhs << " q=" << *this << " rem=0x" << std::hex
                                   << k << std::dec << endl);
        if (is_modulus) {
            setZero();
            m_value[0].m_value = k;
        }
        opCleanThis();
        return *this;
    }

    // +1 word as we may shift during normalization
    uint32_t un[VL_MULS_MAX_WORDS + 1];  // Fixed size, as MSVC++ doesn't allow [words] here
    uint32_t vn[VL_MULS_MAX_WORDS + 1];  // v normalized

    // Zero for ease of debugging and to save having to zero for shifts
    for (int i = 0; i < words; i++) { m_value[i].m_value = 0; }
    for (int i = 0; i < words + 1; i++) { un[i] = vn[i] = 0; }  // +1 as vn may get extra word

    // Algorithm requires divisor MSB to be set
    // Copy and shift to normalize divisor so MSB of vn[vw-1] is set
    const int s = 31 - ((vmsbp1 - 1) & 31);  // shift amount (0...31)
    const uint32_t shift_mask = s ? 0xffffffff : 0;  // otherwise >> 32 won't mask the value
    for (int i = vw - 1; i > 0; i--) {
        vn[i] = (rhs.m_value[i].m_value << s)
                | (shift_mask & (rhs.m_value[i - 1].m_value >> (32 - s)));
    }
    vn[0] = rhs.m_value[0].m_value << s;

    // Copy and shift dividend by same amount; may set new upper word
    if (s) {
        un[uw] = lhs.m_value[uw - 1].m_value >> (32 - s);
    } else {
        un[uw] = 0;
    }
    for (int i = uw - 1; i > 0; i--) {
        un[i] = (lhs.m_value[i].m_value << s)
                | (shift_mask & (lhs.m_value[i - 1].m_value >> (32 - s)));
    }
    un[0] = lhs.m_value[0].m_value << s;

    // printf("  un="); for (int i=5; i>=0; i--) printf(" %08x",un[i]); printf("\n");
    // printf("  vn="); for (int i=5; i>=0; i--) printf(" %08x",vn[i]); printf("\n");
    // printf("  mv="); for (int i=5; i>=0; i--) printf(" %08x",m_value[i]); printf("\n");

    // Main loop
    for (int j = uw - vw; j >= 0; j--) {
        // Estimate
        const uint64_t unw64
            = (static_cast<uint64_t>(un[j + vw]) << 32ULL | static_cast<uint64_t>(un[j + vw - 1]));
        uint64_t qhat = unw64 / static_cast<uint64_t>(vn[vw - 1]);
        uint64_t rhat = unw64 - qhat * static_cast<uint64_t>(vn[vw - 1]);

    again:
        if (qhat >= 0x100000000ULL || ((qhat * vn[vw - 2]) > ((rhat << 32ULL) + un[j + vw - 2]))) {
            qhat = qhat - 1;
            rhat = rhat + vn[vw - 1];
            if (rhat < 0x100000000ULL) goto again;
        }

        int64_t t = 0;  // Must be signed
        uint64_t k = 0;
        for (int i = 0; i < vw; i++) {
            const uint64_t p = qhat * vn[i];  // Multiply by estimate
            t = un[i + j] - k - (p & 0xFFFFFFFFULL);  // Subtract
            un[i + j] = t;
            k = (p >> 32ULL) - (t >> 32ULL);
        }
        t = un[j + vw] - k;
        un[j + vw] = t;
        this->m_value[j].m_value = qhat;  // Save quotient digit

        if (t < 0) {
            // Over subtracted; correct by adding back
            this->m_value[j].m_value--;
            k = 0;
            for (int i = 0; i < vw; i++) {
                t = static_cast<uint64_t>(un[i + j]) + static_cast<uint64_t>(vn[i]) + k;
                un[i + j] = t;
                k = t >> 32ULL;
            }
            un[j + vw] = un[j + vw] + k;
        }
    }

    // printf("  un="); for (int i=5; i>=0; i--) printf(" %08x",un[i]); printf("\n");
    // printf("  vn="); for (int i=5; i>=0; i--) printf(" %08x",vn[i]); printf("\n");
    // printf("  mv="); for (int i=5; i>=0; i--) printf(" %08x",m_value[i]); printf("\n");

    if (is_modulus) {  // modulus
        // Need to reverse normalization on copy to output
        for (int i = 0; i < vw; i++) {
            m_value[i].m_value = (un[i] >> s) | (shift_mask & (un[i + 1] << (32 - s)));
        }
        for (int i = vw; i < words; i++) m_value[i].m_value = 0;
        opCleanThis();
        UINFO(9, "  opmoddiv-mod " << lhs << " " << rhs << " now=" << *this << endl);
        return *this;
    } else {  // division
        opCleanThis();
        UINFO(9, "  opmoddiv-div " << lhs << " " << rhs << " now=" << *this << endl);
        return *this;
    }
}

V3Number& V3Number::opPow(const V3Number& lhs, const V3Number& rhs, bool lsign, bool rsign) {
    // L(i) bit return, if any 4-state, 4-state return
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_LOGIC_ARGS2(lhs, rhs);
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    if (rhs.isEqZero()) return setQuad(1);  // Overrides lhs 0 -> return 0
    // We may want to special case when the lhs is 2, so we can get larger outputs
    if (rsign && rhs.isNegative()) {
        if (lhs.isEqZero()) {
            return setAllBitsXRemoved();
        } else if (lhs.isEqOne()) {
            return setQuad(1);
        } else if (lsign && lhs.isEqAllOnes()) {
            if (rhs.bitIs1(0)) {
                return setAllBits1();  // -1^odd=-1
            } else {
                return setQuad(1);  // -1^even=1
            }
        }
        return setZero();
    }
    if (lhs.isEqZero()) return setZero();
    setZero();
    m_value[0].m_value = 1;
    V3Number power(&lhs, width());
    power.opAssign(lhs);
    for (int bit = 0; bit < rhs.width(); bit++) {
        if (bit > 0) {  // power = power*power
            V3Number lastPower(&lhs, width());
            lastPower.opAssign(power);
            power.opMul(lastPower, lastPower);
        }
        if (rhs.bitIs1(bit)) {  // out *= power
            V3Number lastOut(&lhs, width());
            lastOut.opAssign(*this);
            this->opMul(lastOut, power);
            // UINFO(0, "pow "<<lhs<<" "<<rhs<<" b"<<bit<<" pow="<<power<<" now="<<*this<<endl);
        }
    }
    return *this;
}
V3Number& V3Number::opPowSU(const V3Number& lhs, const V3Number& rhs) {
    return opPow(lhs, rhs, true, false);
}
V3Number& V3Number::opPowSS(const V3Number& lhs, const V3Number& rhs) {
    return opPow(lhs, rhs, true, true);
}
V3Number& V3Number::opPowUS(const V3Number& lhs, const V3Number& rhs) {
    return opPow(lhs, rhs, false, true);
}

V3Number& V3Number::opBufIf1(const V3Number& ens, const V3Number& if1s) {
    NUM_ASSERT_OP_ARGS2(ens, if1s);
    NUM_ASSERT_LOGIC_ARGS2(ens, if1s);
    setZero();
    for (int bit = 0; bit < this->width(); bit++) {
        if (ens.bitIs1(bit)) {
            setBit(bit, if1s.bitIs(bit));
        } else {
            setBit(bit, 'z');
        }
    }
    return *this;
}

V3Number& V3Number::opAssign(const V3Number& lhs) { return opAssignNonXZ(lhs, false); }
V3Number& V3Number::opAssignNonXZ(const V3Number& lhs, bool ignoreXZ) {
    // Note may be a width change during the assign.
    // Special case: opAssign unlike other ops, allows this an assignment
    // to itself; V3Simulate does this when hits "foo=foo;"
    // So no: NUM_ASSERT_OP_ARGS1(lhs);
    if (this != &lhs) {
        setZero();
        if (isString()) {
            m_stringVal = lhs.m_stringVal;
        } else {
            // Also handles double as is just bits
            for (int bit = 0; bit < this->width(); bit++) {
                setBit(bit, ignoreXZ ? lhs.bitIs1(bit) : lhs.bitIs(bit));
            }
        }
    }
    return *this;
}

V3Number& V3Number::opExtendS(const V3Number& lhs, uint32_t lbits) {
    // Note may be a width change during the sign extension
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    setZero();
    for (int bit = 0; bit < width(); bit++) {
        const char extendWith = lhs.bitIsExtend(bit, lbits);
        setBit(bit, extendWith);
    }
    return *this;
}

V3Number& V3Number::opExtendXZ(const V3Number& lhs, uint32_t lbits) {
    // Note may be a width change during the X/Z extension
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    setZero();
    for (int bit = 0; bit < width(); bit++) { setBit(bit, lhs.bitIsExtend(bit, lbits)); }
    return *this;
}

V3Number& V3Number::opClean(const V3Number& lhs, uint32_t bits) { return opSel(lhs, bits - 1, 0); }

void V3Number::opCleanThis(bool warnOnTruncation) {
    // Clean MSB of number
    NUM_ASSERT_LOGIC_ARGS1(*this);
    const ValueAndX v = m_value[words() - 1];
    const uint32_t newValueMsb = v.m_value & hiWordMask();
    const uint32_t newValueXMsb = v.m_valueX & hiWordMask();
    if (warnOnTruncation && (newValueMsb != v.m_value || newValueXMsb != v.m_valueX)) {
        // Displaying in decimal avoids hiWordMask truncation
        v3warn(WIDTH, "Value too large for " << width() << " bit number: " << displayed("%d"));
    }
    m_value[words() - 1] = {newValueMsb, newValueXMsb};
}

V3Number& V3Number::opSel(const V3Number& lhs, const V3Number& msb, const V3Number& lsb) {
    NUM_ASSERT_OP_ARGS3(lhs, msb, lsb);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS2(msb, lsb);
    if (lsb.isFourState() || msb.isFourState()) return setAllBitsX();
    return opSel(lhs, msb.toUInt(), lsb.toUInt());
}

V3Number& V3Number::opSel(const V3Number& lhs, uint32_t msbval, uint32_t lsbval) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    setZero();
    int ibit = lsbval;
    for (int bit = 0; bit < this->width(); bit++) {
        if (ibit >= 0 && ibit < lhs.width() && ibit <= static_cast<int>(msbval)) {
            setBit(bit, lhs.bitIs(ibit));
        } else {
            setBit(bit, 'x');
        }
        ++ibit;
    }
    // UINFO(0,"RANGE "<<lhs<<" "<<msb<<" "<<lsb<<" = "<<*this<<endl);
    return *this;
}

V3Number& V3Number::opSelInto(const V3Number& lhs, const V3Number& lsb, int width) {
    return opSelInto(lhs, lsb.toSInt(), width);
}

V3Number& V3Number::opSelInto(const V3Number& lhs, int lsbval, int width) {
    // this[lsbval+width-1 : lsbval] = lhs;  Other bits of this are not affected
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    int ibit = 0;
    for (int bit = lsbval; bit < lsbval + width; bit++) {
        if (ibit >= 0 && ibit < lhs.width()) {
            setBit(bit, lhs.bitIs(ibit));
        } else {
            setBit(bit, 'x');
        }
        ibit++;
    }
    return *this;
}

//======================================================================
// Ops - Floating point

V3Number& V3Number::opIToRD(const V3Number& lhs, bool isSigned) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(lhs);
    // IEEE says we ignore x/z in real conversions
    V3Number noxz(lhs);
    noxz.opAssignNonXZ(lhs);
    double d = 0;
    const bool negate = isSigned && noxz.isNegative();
    if (negate) {
        const V3Number noxz_signed = noxz;
        noxz.opNegate(noxz_signed);
    }
    for (int bit = noxz.width() - 1; bit >= 0; bit--) {
        // Some precision might be lost in this add, that's what we want
        if (noxz.bitIs1(bit)) d += exp2(bit);
    }
    if (negate) d = -d;
    return setDouble(d);
}
V3Number& V3Number::opRToIS(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_DOUBLE_ARGS1(lhs);
    const double v = VL_TRUNC(lhs.toDouble());
    const int32_t i = static_cast<int32_t>(v);  // C converts from double to int32_t
    return setLongS(i);
}
V3Number& V3Number::opRToIRoundS(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_DOUBLE_ARGS1(lhs);
    const double v = VL_ROUND(lhs.toDouble());
    setZero();
    union {
        double d;
        uint64_t q;
    } u;
    u.d = v;
    if (u.d == 0.0) {}

    const int exp = static_cast<int>((u.q >> 52ULL) & VL_MASK_Q(11)) - 1023;
    const int lsb = exp - 52;
    const uint64_t mantissa = (u.q & VL_MASK_Q(52)) | (1ULL << 52);
    if (v != 0) {
        // IEEE format: [63]=sign [62:52]=exp+1023 [51:0]=mantissa
        // This does not need to support subnormals as they are sub-integral
        for (int bit = 0; bit <= 52; ++bit) {
            if (mantissa & (1ULL << bit)) {
                const int outbit = bit + lsb;
                if (outbit >= 0) setBit(outbit, 1);
            }
        }
        if (v < 0) {
            const V3Number noSign = *this;
            opNegate(noSign);
        }
    }
    return *this;
}
V3Number& V3Number::opRealToBits(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_DOUBLE_ARGS1(lhs);
    // Conveniently our internal format is identical so we can copy bits...
    if (lhs.width() != 64 || this->width() != 64) {
        v3fatalSrc("Real operation on wrong sized number");
    }
    opAssign(lhs);
    m_double = false;
    return *this;
}
V3Number& V3Number::opBitsToRealD(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    // Conveniently our internal format is identical so we can copy bits...
    if (lhs.width() != 64 || this->width() != 64) {
        v3fatalSrc("Real operation on wrong sized number");
    }
    opAssign(lhs);
    m_double = true;
    return *this;
}
V3Number& V3Number::opNegateD(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_DOUBLE_ARGS1(lhs);
    return setDouble(-lhs.toDouble());
}
V3Number& V3Number::opAddD(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_DOUBLE_ARGS2(lhs, rhs);
    return setDouble(lhs.toDouble() + rhs.toDouble());
}
V3Number& V3Number::opSubD(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_DOUBLE_ARGS2(lhs, rhs);
    return setDouble(lhs.toDouble() - rhs.toDouble());
}
V3Number& V3Number::opMulD(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_DOUBLE_ARGS2(lhs, rhs);
    return setDouble(lhs.toDouble() * rhs.toDouble());
}
V3Number& V3Number::opDivD(const V3Number& lhs, const V3Number& rhs) {
    // On exceptions, we just generate 'inf' through floating point
    // IEEE says it's implementation defined what happens
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_DOUBLE_ARGS2(lhs, rhs);
    return setDouble(lhs.toDouble() / rhs.toDouble());
}
V3Number& V3Number::opPowD(const V3Number& lhs, const V3Number& rhs) {
    // On exceptions, we just generate 'inf' through floating point
    // IEEE says it's implementation defined what happens
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_DOUBLE_ARGS2(lhs, rhs);
    return setDouble(pow(lhs.toDouble(), rhs.toDouble()));
}
V3Number& V3Number::opEqD(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_DOUBLE_ARGS2(lhs, rhs);
    return setSingleBits(lhs.toDouble() == rhs.toDouble());
}
V3Number& V3Number::opNeqD(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_DOUBLE_ARGS2(lhs, rhs);
    return setSingleBits(lhs.toDouble() != rhs.toDouble());
}
V3Number& V3Number::opGtD(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_DOUBLE_ARGS2(lhs, rhs);
    return setSingleBits(lhs.toDouble() > rhs.toDouble());
}
V3Number& V3Number::opGteD(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_DOUBLE_ARGS2(lhs, rhs);
    return setSingleBits(lhs.toDouble() >= rhs.toDouble());
}
V3Number& V3Number::opLtD(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_DOUBLE_ARGS2(lhs, rhs);
    return setSingleBits(lhs.toDouble() < rhs.toDouble());
}
V3Number& V3Number::opLteD(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_DOUBLE_ARGS2(lhs, rhs);
    return setSingleBits(lhs.toDouble() <= rhs.toDouble());
}

//======================================================================
// Ops - String

V3Number& V3Number::opConcatN(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_STRING_ARGS2(lhs, rhs);
    return setString(lhs.toString() + rhs.toString());
}
V3Number& V3Number::opReplN(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_STRING_ARGS1(lhs);
    NUM_ASSERT_LOGIC_ARGS1(rhs);
    return opReplN(lhs, rhs.toUInt());
}
V3Number& V3Number::opReplN(const V3Number& lhs, uint32_t rhsval) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_STRING_ARGS1(lhs);
    string out;
    out.reserve(lhs.toString().length() * rhsval);
    for (unsigned times = 0; times < rhsval; times++) { out += lhs.toString(); }
    return setString(out);
}
V3Number& V3Number::opToLowerN(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_STRING_ARGS1(lhs);
    std::string out = lhs.toString();
    for (auto& cr : out) cr = tolower(cr);
    return setString(out);
}
V3Number& V3Number::opToUpperN(const V3Number& lhs) {
    NUM_ASSERT_OP_ARGS1(lhs);
    NUM_ASSERT_STRING_ARGS1(lhs);
    std::string out = lhs.toString();
    for (auto& cr : out) cr = toupper(cr);
    return setString(out);
}

V3Number& V3Number::opEqN(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_STRING_ARGS2(lhs, rhs);
    return setSingleBits(lhs.toString() == rhs.toString());
}
V3Number& V3Number::opNeqN(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_STRING_ARGS2(lhs, rhs);
    return setSingleBits(lhs.toString() != rhs.toString());
}
V3Number& V3Number::opGtN(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_STRING_ARGS2(lhs, rhs);
    return setSingleBits(lhs.toString() > rhs.toString());
}
V3Number& V3Number::opGteN(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_STRING_ARGS2(lhs, rhs);
    return setSingleBits(lhs.toString() >= rhs.toString());
}
V3Number& V3Number::opLtN(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_STRING_ARGS2(lhs, rhs);
    return setSingleBits(lhs.toString() < rhs.toString());
}
V3Number& V3Number::opLteN(const V3Number& lhs, const V3Number& rhs) {
    NUM_ASSERT_OP_ARGS2(lhs, rhs);
    NUM_ASSERT_STRING_ARGS2(lhs, rhs);
    return setSingleBits(lhs.toString() <= rhs.toString());
}
