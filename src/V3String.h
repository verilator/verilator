// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: String manipulation
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#ifndef _V3STRING_H_
#define _V3STRING_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include <string>

//######################################################################
// VString - String manipulation

class VString {
    static bool wildmatchi(const char* s, const char* p);
public:
    // METHODS (generic string utilities)
    // Return true if p with ? or *'s matches s
    static bool wildmatch(const char* s, const char* p);
    // Return {a}{dot}{b}, omitting dot if a or b are empty
    static string dot(const string& a, const string& dot, const string& b);
    // Convert string to lowercase
    static string downcase(const string& str);
    // Replace any %'s with %%
    static string quotePercent(const string& str);
};

//######################################################################
// VHashSha1 - Compute Sha1 hashes

class VHashSha1 {
    // As blocks must be processed in 64 byte chunks, this does not at present
    // support calling input() on multiple non-64B chunks and getting the correct
    // hash. To do that first combine the string before calling here.
    // Or improve to store 0-63 bytes of data between calls to input().

    // MEMBERS
    uint32_t	m_inthash[5];		// Intermediate hash, in host order
    string	m_remainder;		// Unhashed data
    bool	m_final;		// Finalized
    size_t	m_totLength;		// Total all-chunk length as needed by output digest
public:
    // CONSTRUCTORS
    VHashSha1() { init(); }
    explicit VHashSha1(const string& data) { init(); insert(data); }
    ~VHashSha1() {}

    // METHODS
    string digestBinary();		// Return digest as 20 character binary
    string digestHex();			// Return digest formatted as a hex string
    string digestSymbol();		// Return digest formatted as C symbol/base64ish
    uint64_t digestUInt64();		// Return 64-bits of digest
    static void selfTest();		// Test this class

    // Inerting hash data
    void insert(const void* datap, size_t length);  // Process data into the digest
    void insert(const string& data) { insert(data.data(), data.length()); }  // Process data into the digest
    void insert(uint64_t value) { insert(cvtToStr(value)); }

private:
    void init() {
	m_inthash[0] = 0x67452301; m_inthash[1] = 0xefcdab89; m_inthash[2] = 0x98badcfe;
	m_inthash[3] = 0x10325476; m_inthash[4] = 0xc3d2e1f0;
	m_final = false;
	m_totLength = 0;
    }
    static void selfTestOne(const string& data, const string& data2,
			    const string& exp, const string& exp64);
    void finalize();			// Process remaining data
};

//######################################################################
// VName - string which contains a possibly hashed string
// TODO use this wherever there is currently a "string m_name"

class VName {
    string m_name;
    string m_hashed;

    static size_t s_maxLength;		// Length at which to start hashing
    static size_t s_minLength;		// Length to preserve if over maxLength
public:
    // CONSTRUCTORS
    explicit VName(const string& name) : m_name(name) {}
    ~VName() {}
    // METHODS
    void name(const string& name) { m_name = name; m_hashed = ""; }
    string name() const { return m_name; }
    string hashedName();
    // CONFIG STATIC METHORS
    static void maxLength(size_t flag) { s_maxLength=flag; } // Length at which to start hashing, 0=disable
    static size_t maxLength() { return s_maxLength; }
};

//######################################################################

#endif // guard
