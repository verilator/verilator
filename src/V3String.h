// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: String manipulation
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
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
    static bool wildmatch(const char* s, const char* p);
    static string downcase(const string& str);
};

//######################################################################
// Compute FNV1a (Fowler/Noll/Vo) hashes
// See http://www.isthe.com/chongo/tech/comp/fnv/index.html
// Algorithmic basis for these functions was in the public domain, by chongo <Landon Curt Noll>

class VHashFnv {
    enum { FNV1_64_INIT = 0xcbf29ce484222325ULL };  // Initial value
    vluint64_t	m_hash;

    inline void hashC(uint8_t c) {
	m_hash ^= c;
	// Below is faster than m_hash *= 0x100000001b3ULL;
	m_hash += ((m_hash << 1) + (m_hash << 4) + (m_hash << 5)
		   + (m_hash << 7) + (m_hash << 8) + (m_hash << 40));
    }
public:
    VHashFnv() : m_hash(FNV1_64_INIT) {}
    ~VHashFnv() {}

    vluint64_t digestUInt64() const { return m_hash; }

    VHashFnv& insert(const void* bufp, size_t len) {  // Memory
	const uint8_t* bp = (const uint8_t*)bufp;
	const uint8_t* be = bp + len;
	while (bp < be) hashC((vluint64_t)*bp++);
	return *this;
    }
    VHashFnv& insert(const char* strp) {  // String
	const uint8_t* sp = (const uint8_t*)strp;
	while (*sp) hashC((vluint64_t)*sp++);
	return *this;
    }
    VHashFnv& insert(const string& str) { return insert(str.data(), str.length()); }
    VHashFnv& insert(vluint64_t n) {
	hashC(n>>0); hashC(n>>8); hashC(n>>16); hashC(n>>24);
	hashC(n>>32); hashC(n>>40); hashC(n>>48); hashC(n>>56);
	return *this;
    }
    VHashFnv& insert(uint32_t n) {
	hashC(n>>0); hashC(n>>8); hashC(n>>16); hashC(n>>24);
	return *this;
    }
    VHashFnv& insert(uint16_t n) {
	hashC(n>>0); hashC(n>>8);
	return *this;
    }
    VHashFnv& insert(uint8_t n) { hashC(n); return *this; }
    VHashFnv& insert(int n) { hashC((vluint64_t)n); return *this; }
};

//######################################################################

#endif // guard
