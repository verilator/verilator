// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: String manipulation
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

#ifndef VERILATOR_V3STRING_H_
#define VERILATOR_V3STRING_H_

#include "config_build.h"
#include "verilatedos.h"

// No V3 headers here - this is a base class for Vlc etc

#include <iomanip>
#include <map>
#include <sstream>
#include <string>
#include <type_traits>
#include <unordered_map>
#include <vector>

//######################################################################
// Global string-related functions

template <class T>
std::string cvtToStr(const T& t) {
    std::ostringstream os;
    os << t;
    return os.str();
}
template <class T>
typename std::enable_if<std::is_pointer<T>::value, std::string>::type cvtToHex(const T tp) {
    std::ostringstream os;
    os << static_cast<const void*>(tp);
    return os.str();
}
template <class T>
typename std::enable_if<std::is_integral<T>::value, std::string>::type cvtToHex(const T t) {
    std::ostringstream os;
    os << std::hex << std::setw(sizeof(T) * 8 / 4) << std::setfill('0') << t;
    return os.str();
}

inline uint32_t cvtToHash(const void* vp) {
    // We can shove a 64 bit pointer into a 32 bit bucket
    // On 32-bit systems, lower is always 0, but who cares?
    union {
        const void* up;
        struct {
            uint32_t upper;
            uint32_t lower;
        } l;
    } u;
    u.l.upper = 0;
    u.l.lower = 0;
    u.up = vp;
    return u.l.upper ^ u.l.lower;
}

inline string ucfirst(const string& text) {
    string out = text;
    out[0] = toupper(out[0]);
    return out;
}

//######################################################################
// VString - String manipulation

class VString final {
    static bool wildmatchi(const char* s, const char* p);

public:
    // METHODS (generic string utilities)
    // Return true if p with ? or *'s matches s
    static bool wildmatch(const char* s, const char* p);
    // Return true if p with ? or *'s matches s
    static bool wildmatch(const string& s, const string& p);
    // Return {a}{dot}{b}, omitting dot if a or b are empty
    static string dot(const string& a, const string& dot, const string& b);
    // Convert string to lowercase (tolower)
    static string downcase(const string& str);
    // Convert string to upper case (toupper)
    static string upcase(const string& str);
    // Insert esc just before tgt
    static string quoteAny(const string& str, char tgt, char esc);
    // Replace any \'s with \\  (two consecutive backslashes)
    static string quoteBackslash(const string& str) { return quoteAny(str, '\\', '\\'); }
    // Replace any %'s with %%
    static string quotePercent(const string& str) { return quoteAny(str, '%', '%'); }
    // Surround a raw string by double quote and escape if necessary
    // e.g. input abc's  becomes "\"abc\'s\""
    static string quoteStringLiteralForShell(const string& str);
    // Replace any unprintable with space
    // This includes removing tabs, so column tracking is correct
    static string spaceUnprintable(const string& str);
    // Remove any whitespace
    static string removeWhitespace(const string& str);
    // Return true if only whitespace or ""
    static bool isWhitespace(const string& str);
    // Return double by parsing string
    static double parseDouble(const string& str, bool* successp);
    // Replace all occurrences of the word 'from' in 'str' with 'to'. A word is considered
    // to be a consecutive sequence of the characters [a-zA-Z0-9_]. Sub-words are not replaced.
    // e.g.: replaceWords("one apple bad_apple", "apple", "banana") -> "one banana bad_apple"
    static string replaceWord(const string& str, const string& from, const string& to);
    // Predicate to check if 'str' starts with 'prefix'
    static bool startsWith(const string& str, const string& prefix);
};

//######################################################################
// VHashSha256 - Compute Sha256 hashes

class VHashSha256 final {
    // As blocks must be processed in 64 byte chunks, this does not at present
    // support calling input() on multiple non-64B chunks and getting the correct
    // hash. To do that first combine the string before calling here.
    // Or improve to store 0-63 bytes of data between calls to input().

    // MEMBERS
    uint32_t m_inthash[8];  // Intermediate hash, in host order
    string m_remainder;  // Unhashed data
    bool m_final = false;  // Finalized
    size_t m_totLength = 0;  // Total all-chunk length as needed by output digest
public:
    // CONSTRUCTORS
    VHashSha256() {
        m_inthash[0] = 0x6a09e667;
        m_inthash[1] = 0xbb67ae85;
        m_inthash[2] = 0x3c6ef372;
        m_inthash[3] = 0xa54ff53a;
        m_inthash[4] = 0x510e527f;
        m_inthash[5] = 0x9b05688c;
        m_inthash[6] = 0x1f83d9ab;
        m_inthash[7] = 0x5be0cd19;
    }
    explicit VHashSha256(const string& data)
        : VHashSha256{} {
        insert(data);
    }
    ~VHashSha256() = default;

    // METHODS
    string digestBinary();  // Return digest as 32 character binary
    string digestHex();  // Return digest formatted as a hex string
    string digestSymbol();  // Return digest formatted as C symbol/base64ish
    uint64_t digestUInt64();  // Return 64-bits of digest
    static void selfTest();  // Test this class

    // Inerting hash data
    void insert(const void* datap, size_t length);  // Process data into the digest
    void insert(const string& data) {
        insert(data.data(), data.length());
    }  // Process data into the digest
    void insert(uint64_t value) { insert(cvtToStr(value)); }

private:
    static void selfTestOne(const string& data, const string& data2, const string& exp,
                            const string& exp64);
    void finalize();  // Process remaining data
};

//######################################################################
// VName - string which contains a possibly hashed string
// TODO use this wherever there is currently a "string m_name"

class VName final {
    string m_name;
    string m_hashed;
    static std::map<string, string> s_dehashMap;  // hashed -> original decoder

    static size_t s_maxLength;  // Length at which to start hashing
    static size_t s_minLength;  // Length to preserve if over maxLength

public:
    // CONSTRUCTORS
    explicit VName(const string& name)
        : m_name{name} {}
    ~VName() = default;
    // METHODS
    void name(const string& name) {
        m_name = name;
        m_hashed = "";
    }
    string name() const { return m_name; }
    string hashedName();
    // CONFIG STATIC METHODS
    // Length at which to start hashing, 0=disable
    static void maxLength(size_t flag) { s_maxLength = flag; }
    static size_t maxLength() { return s_maxLength; }
    static string dehash(const string& in);
};

//######################################################################
// VSpellCheck - Find near-match spelling suggestions given list of possibilities

class VSpellCheck final {
    // CONSTANTS
    static constexpr unsigned NUM_CANDIDATE_LIMIT = 10000;  // Avoid searching huge netlists
    static constexpr unsigned LENGTH_LIMIT = 100;  // Maximum string length to search
    // TYPES
    using EditDistance = unsigned int;
    // MEMBERS
    std::vector<std::string> m_candidates;  // Strings we try to match
public:
    // CONSTRUCTORS
    VSpellCheck() = default;
    ~VSpellCheck() = default;
    // METHODS
    // Push a symbol table value to be considered as a candidate
    // The first item pushed has highest priority, all else being equal
    void pushCandidate(const string& s) {
        if (m_candidates.size() < NUM_CANDIDATE_LIMIT) m_candidates.push_back(s);
    }
    // Return candidate is closest to provided string, or "" for none
    string bestCandidate(const string& goal) const {
        EditDistance dist;
        return bestCandidateInfo(goal, dist /*ref*/);
    }
    // Return friendly message
    string bestCandidateMsg(const string& goal) const {
        const string candidate = bestCandidate(goal);
        if (candidate.empty()) {
            return "";
        } else {
            return std::string{"... Suggested alternative: '"} + candidate + "'";
        }
    }
    static void selfTest();

private:
    static EditDistance editDistance(const string& s, const string& t);
    static EditDistance cutoffDistance(size_t goal_len, size_t candidate_len);
    string bestCandidateInfo(const string& goal, EditDistance& distancer) const;
    static void selfTestDistanceOne(const string& a, const string& b, EditDistance expected);
    static void selfTestSuggestOne(bool matches, const string& c, const string& goal,
                                   EditDistance dist);
};

//######################################################################

#endif  // guard
