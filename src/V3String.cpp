// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Options parsing
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3String.h"
#include "V3Error.h"

size_t VName::s_minLength = 32;
size_t VName::s_maxLength = 0;	// Disabled

//######################################################################
// Wildcard

// Double procedures, inlined, unrolls loop much better
inline bool VString::wildmatchi(const char* s, const char* p) {
    for ( ; *p; s++, p++) {
	if (*p!='*') {
	    if (((*s)!=(*p)) && *p != '?')
		return false;
	}
	else {
	    // Trailing star matches everything.
	    if (!*++p) return true;
            while (!wildmatch(s, p)) {
                if (*++s == '\0') {
                    return false;
                }
            }
	    return true;
	}
    }
    return (*s == '\0');
}

bool VString::wildmatch(const char* s, const char* p) {
    for ( ; *p; s++, p++) {
	if (*p!='*') {
	    if (((*s)!=(*p)) && *p != '?')
		return false;
	}
	else {
	    // Trailing star matches everything.
	    if (!*++p) return true;
            while (!wildmatchi(s, p)) {
                if (*++s == '\0') {
                    return false;
                }
            }
	    return true;
	}
    }
    return (*s == '\0');
}

string VString::dot(const string& a, const string& dot, const string& b) {
    if (b=="") return a;
    if (a=="") return b;
    return a+dot+b;
}

string VString::downcase(const string& str) {
    string out = str;
    for (string::iterator pos = out.begin(); pos != out.end(); ++pos) {
	*pos = tolower(*pos);
    }
    return out;
}

string VString::quotePercent(const string& str) {
    string out;
    for (string::const_iterator pos = str.begin(); pos != str.end(); ++pos) {
	if (*pos == '%') out += '%';
	out += *pos;
    }
    return out;
}

//######################################################################
// VHashSha1

static inline uint32_t sha1Rotl32(uint32_t lhs, uint32_t rhs) VL_ATTR_ALWINLINE;
static inline uint32_t sha1Rotl32(uint32_t lhs, uint32_t rhs) {
    return ((lhs << rhs) | (lhs >> (32 - rhs)));
}

static inline void sha1Block(uint32_t* h, uint32_t* w) VL_ATTR_ALWINLINE;
static inline void sha1Block(uint32_t* h, uint32_t* w) {
#define SHA1ITER(func, roundConst) do { \
	    uint32_t t = sha1Rotl32(a, 5) + (func) + e + (roundConst) + w[round]; \
	    e = d;  d = c;  c = sha1Rotl32(b, 30);  b = a;  a = t; \
	} while (0)

    uint32_t a = h[0];
    uint32_t b = h[1];
    uint32_t c = h[2];
    uint32_t d = h[3];
    uint32_t e = h[4];
    int round = 0;

    for (; round < 16; ++round) {
	SHA1ITER((b & c) | (~b & d), 0x5a827999);
    }
    for (; round < 20; ++round) {
	w[round] = sha1Rotl32((w[round - 3] ^ w[round - 8] ^ w[round - 14] ^ w[round - 16]), 1);
	SHA1ITER((b & c) | (~b & d), 0x5a827999);
    }
    for (; round < 40; ++round) {
	w[round] = sha1Rotl32((w[round - 3] ^ w[round - 8] ^ w[round - 14] ^ w[round - 16]), 1);
	SHA1ITER(b ^ c ^ d, 0x6ed9eba1);
    }
    for (; round < 60; ++round) {
	w[round] = sha1Rotl32((w[round - 3] ^ w[round - 8] ^ w[round - 14] ^ w[round - 16]), 1);
	SHA1ITER((b & c) | (b & d) | (c & d), 0x8f1bbcdc);
    }
    for (; round < 80; ++round) {
	w[round] = sha1Rotl32((w[round - 3] ^ w[round - 8] ^ w[round - 14] ^ w[round - 16]), 1);
	SHA1ITER(b ^ c ^ d, 0xca62c1d6);
    }

    h[0] += a;
    h[1] += b;
    h[2] += c;
    h[3] += d;
    h[4] += e;
#undef SHA1ITER
}

void VHashSha1::insert(const void* datap, size_t length) {
    UASSERT(!m_final, "Called VHashSha1::insert after finalized the hash value");
    m_totLength += length;

    string tempData;
    int chunkLen;
    const uint8_t* chunkp;
    if (m_remainder=="") {
        chunkLen = length;
        chunkp = static_cast<const uint8_t*>(datap);
    } else {
	// If there are large inserts it would be more efficient to avoid this copy
	// by copying bytes in the loop below from either m_remainder or the data
	// as appropriate.
        tempData = m_remainder + string(static_cast<const char*>(datap), length);
        chunkLen = tempData.length();
        chunkp = reinterpret_cast<const uint8_t*>(tempData.data());
    }

    // See wikipedia SHA-1 algorithm summary
    uint32_t w[80];	// Round buffer, [0..15] are input data, rest used by rounds
    int posBegin = 0;	// Position in buffer for start of this block
    int posEnd = 0;	// Position in buffer for end of this block

    // Process complete 64-byte blocks
    while (posBegin <= chunkLen - 64) {
	posEnd = posBegin + 64;
	// 64 byte round input data, being careful to swap on big, keep on little
	for (int roundByte = 0; posBegin < posEnd; posBegin += 4) {
            w[roundByte++] = (static_cast<uint32_t>(chunkp[posBegin + 3])
                              | (static_cast<uint32_t>(chunkp[posBegin + 2]) << 8)
                              | (static_cast<uint32_t>(chunkp[posBegin + 1]) << 16)
                              | (static_cast<uint32_t>(chunkp[posBegin]) << 24));
	}
	sha1Block(m_inthash, w);
    }

    m_remainder = string(reinterpret_cast<const char*>(chunkp+posBegin), chunkLen-posEnd);
}

void VHashSha1::finalize() {
    if (!m_final) {
	// Make sure no 64 byte blocks left
	insert("");
	m_final = true;

	// Process final possibly non-complete 64-byte block
	uint32_t w[80];	// Round buffer, [0..15] are input data, rest used by rounds
	for (int i=0; i<16; ++i) w[i] = 0;
	size_t blockPos = 0;
	for (; blockPos < m_remainder.length(); ++blockPos) {
            w[blockPos >> 2] |= ((static_cast<uint32_t>(m_remainder[blockPos]))
                                 << ((3 - (blockPos & 3)) << 3));
	}
	w[blockPos >> 2] |= 0x80 << ((3 - (blockPos & 3)) << 3);
	if (m_remainder.length() >= 56) {
	    sha1Block(m_inthash, w);
	    for (int i=0; i<16; ++i) w[i] = 0;
	}
	w[15] = m_totLength << 3;
	sha1Block(m_inthash, w);

	m_remainder.clear();
    }
}

string VHashSha1::digestBinary() {
    finalize();
    string out; out.reserve(20);
    for (size_t i=0; i<20; ++i) {
        out += (m_inthash[i >> 2] >> (((3 - i) & 0x3) << 3)) & 0xff;
    }
    return out;
}

uint64_t VHashSha1::digestUInt64() {
    const string& binhash = digestBinary();
    uint64_t out = 0;
    for (size_t byte=0; byte<sizeof(uint64_t); ++byte) {
        unsigned char c = binhash[byte];
        out = (out<<8) | c;
    }
    return out;
}

string VHashSha1::digestHex() {
    static const char digits[16+1] = "0123456789abcdef";
    const string& binhash = digestBinary();
    string out; out.reserve(40);
    for (size_t byte=0; byte<20; ++byte) {
	out += digits[ (binhash[byte]>>4) & 0xf ];
	out += digits[ (binhash[byte]>>0) & 0xf ];
    }
    return out;
}

string VHashSha1::digestSymbol() {
    // Make a symbol name from hash.  Similar to base64, however base 64
    // has + and / for last two digits, but need C symbol, and we also
    // avoid conflicts with use of _, so use "AB" at the end.
    // Thus this function is non-reversable.
    static const char digits[64+1] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789AB";
    const string& binhash = digestBinary();
    string out; out.reserve(28);
    int pos = 0;
    for (; pos < (160/8) - 2; pos += 3) {
	out += digits[((binhash[pos] >> 2) & 0x3f)];
	out += digits[((binhash[pos] & 0x3) << 4)
                      | (static_cast<int>(binhash[pos + 1] & 0xf0) >> 4)];
	out += digits[((binhash[pos + 1] & 0xf) << 2)
                      | (static_cast<int>(binhash[pos + 2] & 0xc0) >> 6)];
	out += digits[((binhash[pos + 2] & 0x3f))];
    }
    if (0) { // Not needed for 160 bit hash
	out += digits[((binhash[pos] >> 2) & 0x3f)];
	out += digits[((binhash[pos] & 0x3) << 4)];
    }
    else {
	out += digits[((binhash[pos] >> 2) & 0x3f)];
	out += digits[((binhash[pos] & 0x3) << 4)
                      | (static_cast<int>(binhash[pos + 1] & 0xf0) >> 4)];
	out += digits[((binhash[pos + 1] & 0xf) << 2)];
    }
    return out;
}

void VHashSha1::selfTestOne(const string& data, const string& data2,
			     const string& exp, const string& exp64) {
    VHashSha1 digest (data);
    if (data2!="") digest.insert(data2);
    if (digest.digestHex() != exp) {
        std::cerr << "%Error: When hashing '"<<data+data2<<"'"<<endl;
        std::cerr << "%Error: got="<<digest.digestHex()<<endl;
        std::cerr << "%Error: exp="<<exp<<endl;
    }
    if (digest.digestSymbol() != exp64) {
        std::cerr << "%Error: When hashing '"<<data+data2<<"'"<<endl;
        std::cerr << "%Error: got="<<digest.digestSymbol()<<endl;
        std::cerr << "%Error: exp="<<exp64<<endl;
    }
}

void VHashSha1::selfTest() {
    selfTestOne("", "",
		"da39a3ee5e6b4b0d3255bfef95601890afd80709",
		"2jmj7l5rSw0yVbBvlWAYkKBYBwk");
    selfTestOne("a", "",
		"86f7e437faa5a7fce15d1ddcb9eaeaea377667b8",
		"hvfkNBqlpBzhXR3cuerq6jd2Z7g");
    selfTestOne("The quick brown fox jumps over the lazy dog", "",
		"2fd4e1c67a2d28fced849ee1bb76e7391b93eb12",
		"L9ThxnotKPzthJ7hu3bnORuT6xI");
    selfTestOne("The quick brown fox jumps over the lazy"," dog",
		"2fd4e1c67a2d28fced849ee1bb76e7391b93eb12",
		"L9ThxnotKPzthJ7hu3bnORuT6xI");
    selfTestOne("Test using larger than block-size key and larger than one block-size data", "",
		"9026e8faed6ef4ec5ae3ff049020d7f0af7abbbf",
		"kCboAu1u9Oxa4B8EkCDX8K96u78");
    selfTestOne("Test using", " larger than block-size key and larger than one block-size data",
		"9026e8faed6ef4ec5ae3ff049020d7f0af7abbbf",
		"kCboAu1u9Oxa4B8EkCDX8K96u78");
}

//######################################################################
// VName

string VName::hashedName() {
    if (m_name=="") return "";
    if (m_hashed!="") return m_hashed; // Memoized
    if (s_maxLength==0 || m_name.length() < s_maxLength) {
	m_hashed = m_name;
	return m_hashed;
    } else {
	VHashSha1 hash(m_name);
	string suffix = "__Vhsh"+hash.digestSymbol();
	if (s_minLength < s_maxLength) {
	    m_hashed = m_name.substr(0,s_minLength) + suffix;
	} else {
	    m_hashed = suffix;
	}
	return m_hashed;
    }
}
