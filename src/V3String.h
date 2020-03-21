// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: String manipulation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3STRING_H_
#define _V3STRING_H_ 1

#include "config_build.h"
#include "verilatedos.h"

// No V3 headers here - this is a base class for Vlc etc

#include <string>
#include <sstream>
#include <vector>

//######################################################################
// Global string-related functions

template <class T> std::string cvtToStr(const T& t) {
    std::ostringstream os; os<<t; return os.str();
}
template <class T> std::string cvtToHex(const T* tp) {
    std::ostringstream os; os<<static_cast<const void*>(tp); return os.str();
}

inline uint32_t cvtToHash(const void* vp) {
    // We can shove a 64 bit pointer into a 32 bit bucket
    // On 32-bit systems, lower is always 0, but who cares?
    union { const void* up; struct {uint32_t upper; uint32_t lower;} l;} u;
    u.l.upper = 0; u.l.lower = 0; u.up = vp;
    return u.l.upper^u.l.lower;
}

inline string ucfirst(const string& text) {
    string out = text;
    out[0] = toupper(out[0]);
    return out;
}

//######################################################################
// VString - String manipulation

class VString {
    static bool wildmatchi(const char* s, const char* p);
public:
    // METHODS (generic string utilities)
    // Return true if p with ? or *'s matches s
    static bool wildmatch(const char* s, const char* p);
    // Return true if p with ? or *'s matches s
    static bool wildmatch(const string& s, const string& p);
    // Return true if this is a wildcard string (contains * or ?)
    static bool isWildcard(const string &p);
    // Return {a}{dot}{b}, omitting dot if a or b are empty
    static string dot(const string& a, const string& dot, const string& b);
    // Convert string to lowercase (tolower)
    static string downcase(const string& str);
    // Convert string to upper case (toupper)
    static string upcase(const string& str);
    // Replace any %'s with %%
    static string quotePercent(const string& str);
    // Replace any unprintable with space
    // This includes removing tabs, so column tracking is correct
    static string spaceUnprintable(const string& str);
    // Return true if only whitespace or ""
    static bool isWhitespace(const string& str);
};

//######################################################################
// VHashSha256 - Compute Sha256 hashes

class VHashSha256 {
    // As blocks must be processed in 64 byte chunks, this does not at present
    // support calling input() on multiple non-64B chunks and getting the correct
    // hash. To do that first combine the string before calling here.
    // Or improve to store 0-63 bytes of data between calls to input().

    // MEMBERS
    uint32_t    m_inthash[8];           // Intermediate hash, in host order
    string      m_remainder;            // Unhashed data
    bool        m_final;                // Finalized
    size_t      m_totLength;            // Total all-chunk length as needed by output digest
public:
    // CONSTRUCTORS
    VHashSha256() { init(); }
    explicit VHashSha256(const string& data) { init(); insert(data); }
    ~VHashSha256() {}

    // METHODS
    string digestBinary();  // Return digest as 32 character binary
    string digestHex();  // Return digest formatted as a hex string
    string digestSymbol();  // Return digest formatted as C symbol/base64ish
    uint64_t digestUInt64();  // Return 64-bits of digest
    static void selfTest();  // Test this class

    // Inerting hash data
    void insert(const void* datap, size_t length);  // Process data into the digest
    void insert(const string& data) { insert(data.data(), data.length()); }  // Process data into the digest
    void insert(uint64_t value) { insert(cvtToStr(value)); }

private:
    void init() {
        m_inthash[0] = 0x6a09e667; m_inthash[1] = 0xbb67ae85;
        m_inthash[2] = 0x3c6ef372; m_inthash[3] = 0xa54ff53a;
        m_inthash[4] = 0x510e527f; m_inthash[5] = 0x9b05688c;
        m_inthash[6] = 0x1f83d9ab; m_inthash[7] = 0x5be0cd19;
        m_final = false;
        m_totLength = 0;
    }
    static void selfTestOne(const string& data, const string& data2,
                            const string& exp, const string& exp64);
    void finalize();  // Process remaining data
};

//######################################################################
// VName - string which contains a possibly hashed string
// TODO use this wherever there is currently a "string m_name"

class VName {
    string m_name;
    string m_hashed;

    static size_t s_maxLength;  // Length at which to start hashing
    static size_t s_minLength;  // Length to preserve if over maxLength
public:
    // CONSTRUCTORS
    explicit VName(const string& name) : m_name(name) {}
    ~VName() {}
    // METHODS
    void name(const string& name) { m_name = name; m_hashed = ""; }
    string name() const { return m_name; }
    string hashedName();
    // CONFIG STATIC METHODS
    // Length at which to start hashing, 0=disable
    static void maxLength(size_t flag) { s_maxLength = flag; }
    static size_t maxLength() { return s_maxLength; }
};

//######################################################################
// VSpellCheck - Find near-match spelling suggestions given list of possibilities

class VSpellCheck {
    // CONSTANTS
    enum { NUM_CANDIDATE_LIMIT = 10000 };  // Avoid searching huge netlists
    enum { LENGTH_LIMIT = 100 };  // Maximum string length to search
    // TYPES
    typedef unsigned int EditDistance;
    typedef std::vector<string> Candidates;
    // MEMBERS
    Candidates m_candidates;  // Strings we try to match
public:
    // CONSTRUCTORS
    explicit VSpellCheck() {}
    ~VSpellCheck() {}
    // METHODS
    // Push a symbol table value to be considered as a candidate
    // The first item pushed has highest priority, all else being equal
    void pushCandidate(const string& s) {
        if (m_candidates.size() < NUM_CANDIDATE_LIMIT) m_candidates.push_back(s);
    }
    // Return candidate is closest to provided string, or "" for none
    string bestCandidate(const string& goal) {
        EditDistance dist;
        return bestCandidateInfo(goal, dist/*ref*/);
    }
    // Return friendly message
    string bestCandidateMsg(const string& goal) {
        string candidate = bestCandidate(goal);
        if (candidate.empty()) return "";
        else return string("... Suggested alternative: '")+candidate+"'";
    }
    static void selfTest();
private:
    static EditDistance editDistance(const string& s, const string& t);
    static EditDistance cutoffDistance(size_t goal_len, size_t candidate_len);
    string bestCandidateInfo(const string& goal, EditDistance& distancer);
    static void selfTestDistanceOne(const string& a, const string& b,
                                    EditDistance expected);
    static void selfTestSuggestOne(bool matches, const string& c, const string& goal,
                                   EditDistance dist);
};

//######################################################################

#endif  // guard
