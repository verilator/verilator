// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Options parsing
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

// Limited V3 headers here - this is a base class for Vlc etc
#include "V3Error.h"
#include "V3String.h"

#include <algorithm>

size_t VName::s_minLength = 32;
size_t VName::s_maxLength = 0;  // Disabled
std::map<string, string> VName::s_dehashMap;

//######################################################################
// Wildcard

// Double procedures, inlined, unrolls loop much better
inline bool VString::wildmatchi(const char* s, const char* p) {
    for (; *p; s++, p++) {
        if (*p != '*') {
            if (((*s) != (*p)) && *p != '?') return false;
        } else {
            // Trailing star matches everything.
            if (!*++p) return true;
            while (!wildmatch(s, p)) {
                if (*++s == '\0') return false;
            }
            return true;
        }
    }
    return (*s == '\0');
}

bool VString::wildmatch(const char* s, const char* p) {
    for (; *p; s++, p++) {
        if (*p != '*') {
            if (((*s) != (*p)) && *p != '?') return false;
        } else {
            // Trailing star matches everything.
            if (!*++p) return true;
            while (!wildmatchi(s, p)) {
                if (*++s == '\0') return false;
            }
            return true;
        }
    }
    return (*s == '\0');
}

bool VString::wildmatch(const string& s, const string& p) {
    return wildmatch(s.c_str(), p.c_str());
}

string VString::dot(const string& a, const string& dot, const string& b) {
    if (b == "") return a;
    if (a == "") return b;
    return a + dot + b;
}

string VString::downcase(const string& str) {
    string out = str;
    for (auto& cr : out) cr = tolower(cr);
    return out;
}

string VString::upcase(const string& str) {
    string out = str;
    for (auto& cr : out) cr = toupper(cr);
    return out;
}

string VString::quoteAny(const string& str, char tgt, char esc) {
    string out;
    for (const char c : str) {
        if (c == tgt) out += esc;
        out += c;
    }
    return out;
}

string VString::quoteStringLiteralForShell(const string& str) {
    string result;
    const char dquote = '"';
    const char escape = '\\';
    result.push_back(dquote);  // Start quoted string
    result.push_back(escape);
    result.push_back(dquote);  // "
    for (const char c : str) {
        if (c == dquote || c == escape) result.push_back(escape);
        result.push_back(c);
    }
    result.push_back(escape);
    result.push_back(dquote);  // "
    result.push_back(dquote);  // Terminate quoted string
    return result;
}

string VString::spaceUnprintable(const string& str) {
    string out;
    for (const char c : str) {
        if (isprint(c)) {
            out += c;
        } else {
            out += ' ';
        }
    }
    return out;
}

string VString::removeWhitespace(const string& str) {
    string out;
    out.reserve(str.size());
    for (const char c : str) {
        if (!isspace(c)) out += c;
    }
    return out;
}

bool VString::isWhitespace(const string& str) {
    for (const char c : str) {
        if (!isspace(c)) return false;
    }
    return true;
}

double VString::parseDouble(const string& str, bool* successp) {
    char* const strgp = new char[str.size() + 1];
    char* dp = strgp;
    if (successp) *successp = true;
    for (const char* sp = str.c_str(); *sp; ++sp) {
        if (*sp != '_') *dp++ = *sp;
    }
    *dp++ = '\0';
    char* endp = strgp;
    const double d = strtod(strgp, &endp);
    const size_t parsed_len = endp - strgp;
    if (parsed_len != strlen(strgp)) {
        if (successp) *successp = false;
    }
    VL_DO_DANGLING(delete[] strgp, strgp);
    return d;
}

static bool isWordChar(char c) { return isalnum(c) || c == '_'; }

string VString::replaceWord(const string& str, const string& from, const string& to) {
    string result = str;
    const size_t len = from.size();
    UASSERT_STATIC(len > 0, "Cannot replace empty string");
    for (size_t pos = 0; (pos = result.find(from, pos)) != string::npos; pos += len) {
        // Only replace whole words
        if (((pos > 0) && isWordChar(result[pos - 1])) ||  //
            ((pos + len < result.size()) && isWordChar(result[pos + len]))) {
            continue;
        }
        result.replace(pos, len, to);
    }
    return result;
}

bool VString::startsWith(const string& str, const string& prefix) {
    return str.rfind(prefix, 0) == 0;  // Faster than .find(_) == 0
}

//######################################################################
// VHashSha256

static const uint32_t sha256K[]
    = {0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
       0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
       0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
       0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
       0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
       0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
       0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
       0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
       0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
       0xc67178f2};

static inline uint32_t shaRotr32(uint32_t lhs, uint32_t rhs) VL_ATTR_ALWINLINE;
static inline uint32_t shaRotr32(uint32_t lhs, uint32_t rhs) {
    return lhs >> rhs | lhs << (32 - rhs);
}

static inline void sha256Block(uint32_t* h, const uint32_t* chunk) VL_ATTR_ALWINLINE;
static inline void sha256Block(uint32_t* h, const uint32_t* chunk) {
    uint32_t ah[8];
    const uint32_t* p = chunk;

    // Initialize working variables to current hash value
    for (unsigned i = 0; i < 8; i++) ah[i] = h[i];
    // Compression function main loop
    for (unsigned i = 0; i < 4; ++i) {
        uint32_t w[16];

        for (unsigned j = 0; j < 16; ++j) {
            if (i == 0) {
                w[j] = *p++;
            } else {
                // Extend the first 16 words into the remaining
                // 48 words w[16..63] of the message schedule array:
                const uint32_t s0 = shaRotr32(w[(j + 1) & 0xf], 7)
                                    ^ shaRotr32(w[(j + 1) & 0xf], 18) ^ (w[(j + 1) & 0xf] >> 3);
                const uint32_t s1 = shaRotr32(w[(j + 14) & 0xf], 17)
                                    ^ shaRotr32(w[(j + 14) & 0xf], 19) ^ (w[(j + 14) & 0xf] >> 10);
                w[j] = w[j] + s0 + w[(j + 9) & 0xf] + s1;
            }
            const uint32_t s1 = shaRotr32(ah[4], 6) ^ shaRotr32(ah[4], 11) ^ shaRotr32(ah[4], 25);
            const uint32_t ch = (ah[4] & ah[5]) ^ (~ah[4] & ah[6]);
            const uint32_t temp1 = ah[7] + s1 + ch + sha256K[i << 4 | j] + w[j];
            const uint32_t s0 = shaRotr32(ah[0], 2) ^ shaRotr32(ah[0], 13) ^ shaRotr32(ah[0], 22);
            const uint32_t maj = (ah[0] & ah[1]) ^ (ah[0] & ah[2]) ^ (ah[1] & ah[2]);
            const uint32_t temp2 = s0 + maj;

            ah[7] = ah[6];
            ah[6] = ah[5];
            ah[5] = ah[4];
            ah[4] = ah[3] + temp1;
            ah[3] = ah[2];
            ah[2] = ah[1];
            ah[1] = ah[0];
            ah[0] = temp1 + temp2;
        }
    }
    for (unsigned i = 0; i < 8; ++i) h[i] += ah[i];
}

void VHashSha256::insert(const void* datap, size_t length) {
    UASSERT(!m_final, "Called VHashSha256::insert after finalized the hash value");
    m_totLength += length;

    string tempData;
    int chunkLen;
    const uint8_t* chunkp;
    if (m_remainder == "") {
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
    uint32_t w[64];  // Round buffer, [0..15] are input data, rest used by rounds
    int posBegin = 0;  // Position in buffer for start of this block
    int posEnd = 0;  // Position in buffer for end of this block

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
        sha256Block(m_inthash, w);
    }

    m_remainder = string(reinterpret_cast<const char*>(chunkp + posBegin), chunkLen - posEnd);
}

void VHashSha256::finalize() {
    if (!m_final) {
        // Make sure no 64 byte blocks left
        insert("");
        m_final = true;

        // Process final possibly non-complete 64-byte block
        uint32_t w[16];  // Round buffer, [0..15] are input data
        for (int i = 0; i < 16; ++i) w[i] = 0;
        size_t blockPos = 0;
        for (; blockPos < m_remainder.length(); ++blockPos) {
            w[blockPos >> 2]
                |= ((static_cast<uint32_t>(m_remainder[blockPos])) << ((3 - (blockPos & 3)) << 3));
        }
        w[blockPos >> 2] |= 0x80 << ((3 - (blockPos & 3)) << 3);
        if (m_remainder.length() >= 56) {
            sha256Block(m_inthash, w);
            for (int i = 0; i < 16; ++i) w[i] = 0;
        }
        w[15] = m_totLength << 3;
        sha256Block(m_inthash, w);

        m_remainder.clear();
    }
}

string VHashSha256::digestBinary() {
    finalize();
    string out;
    out.reserve(32);
    for (size_t i = 0; i < 32; ++i) {
        out += (m_inthash[i >> 2] >> (((3 - i) & 0x3) << 3)) & 0xff;
    }
    return out;
}

uint64_t VHashSha256::digestUInt64() {
    const string& binhash = digestBinary();
    uint64_t out = 0;
    for (size_t byte = 0; byte < sizeof(uint64_t); ++byte) {
        const unsigned char c = binhash[byte];
        out = (out << 8) | c;
    }
    return out;
}

string VHashSha256::digestHex() {
    static const char* const digits = "0123456789abcdef";
    const string& binhash = digestBinary();
    string out;
    out.reserve(70);
    for (size_t byte = 0; byte < 32; ++byte) {
        out += digits[(binhash[byte] >> 4) & 0xf];
        out += digits[(binhash[byte] >> 0) & 0xf];
    }
    return out;
}

string VHashSha256::digestSymbol() {
    // Make a symbol name from hash.  Similar to base64, however base 64
    // has + and / for last two digits, but need C symbol, and we also
    // avoid conflicts with use of _, so use "AB" at the end.
    // Thus this function is non-reversible.
    static const char* const digits
        = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789AB";
    const string& binhash = digestBinary();
    string out;
    out.reserve(28);
    int pos = 0;
    for (; pos < (256 / 8) - 2; pos += 3) {
        out += digits[((binhash[pos] >> 2) & 0x3f)];
        out += digits[((binhash[pos] & 0x3) << 4)
                      | (static_cast<int>(binhash[pos + 1] & 0xf0) >> 4)];
        out += digits[((binhash[pos + 1] & 0xf) << 2)
                      | (static_cast<int>(binhash[pos + 2] & 0xc0) >> 6)];
        out += digits[((binhash[pos + 2] & 0x3f))];
    }
    // Any leftover bits don't matter for our purpose
    return out;
}

void VHashSha256::selfTestOne(const string& data, const string& data2, const string& exp,
                              const string& exp64) {
    VHashSha256 digest(data);
    if (data2 != "") digest.insert(data2);
    if (VL_UNCOVERABLE(digest.digestHex() != exp)) {
        std::cerr << "%Error: When hashing '" << data + data2 << "'\n"  // LCOV_EXCL_LINE
                  << "        ... got=" << digest.digestHex() << '\n'  // LCOV_EXCL_LINE
                  << "        ... exp=" << exp << endl;  // LCOV_EXCL_LINE
    }
    if (VL_UNCOVERABLE(digest.digestSymbol() != exp64)) {
        std::cerr << "%Error: When hashing '" << data + data2 << "'\n"  // LCOV_EXCL_LINE
                  << "        ... got=" << digest.digestSymbol() << '\n'  // LCOV_EXCL_LINE
                  << "        ... exp=" << exp64 << endl;  // LCOV_EXCL_LINE
    }
}

void VHashSha256::selfTest() {
    selfTestOne("", "", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
                "47DEQpj8HBSaABTImWA5JCeuQeRkm5NMpJWZG3hS");
    selfTestOne("a", "", "ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb",
                "ypeBEsobvcr6wjGzmiPcTaeG7BgUfE5yuYB3haBu");
    selfTestOne("The quick brown fox jumps over the lazy dog", "",
                "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592",
                "16j7swfXgJRpypq8sAguT41WUeRtPNt2LQLQvzfJ");
    selfTestOne("The quick brown fox jumps over the lazy", " dog",
                "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592",
                "16j7swfXgJRpypq8sAguT41WUeRtPNt2LQLQvzfJ");
    selfTestOne("Test using larger than block-size key and larger than one block-size data", "",
                "9dc35674a024b28e8440080b5331652e985f2d61d7a1fca80a648b7f9ffa0dd3",
                "ncNWdKAkso6EQAgLUzFlLphfLWHXofyoCmSLf5B6");
    selfTestOne("Test using", " larger than block-size key and larger than one block-size data",
                "9dc35674a024b28e8440080b5331652e985f2d61d7a1fca80a648b7f9ffa0dd3",
                "ncNWdKAkso6EQAgLUzFlLphfLWHXofyoCmSLf5B6");
}

//######################################################################
// VName

string VName::dehash(const string& in) {
    static const char VHSH[] = "__Vhsh";
    static const size_t DOT_LEN = strlen("__DOT__");
    std::string dehashed;

    // Need to split 'in' into components separated by __DOT__, 'last_dot_pos'
    // keeps track of the position after the most recently found instance of __DOT__
    for (string::size_type last_dot_pos = 0; last_dot_pos < in.size();) {
        const string::size_type next_dot_pos = in.find("__DOT__", last_dot_pos);
        // Two iterators defining the range between the last and next dots.
        const auto search_begin = std::begin(in) + last_dot_pos;
        const auto search_end
            = next_dot_pos == string::npos ? std::end(in) : std::begin(in) + next_dot_pos;

        // Search for __Vhsh between the two dots.
        const auto begin_vhsh
            = std::search(search_begin, search_end, std::begin(VHSH), std::end(VHSH) - 1);
        if (begin_vhsh != search_end) {
            const std::string vhsh(begin_vhsh, search_end);
            const auto& it = s_dehashMap.find(vhsh);
            UASSERT(it != s_dehashMap.end(), "String not in reverse hash map '" << vhsh << "'");
            // Is this not the first component, but the first to require dehashing?
            if (last_dot_pos > 0 && dehashed.empty()) {
                // Seed 'dehashed' with the previously processed components.
                dehashed = in.substr(0, last_dot_pos);
            }
            // Append the unhashed part of the component.
            dehashed += std::string(search_begin, begin_vhsh);
            // Append the bit that was lost to truncation but retrieved from the dehash map.
            dehashed += it->second;
        }
        // This component doesn't need dehashing but a previous one might have.
        else if (!dehashed.empty()) {
            dehashed += std::string(search_begin, search_end);
        }

        if (next_dot_pos != string::npos) {
            // Is there a __DOT__ to add to the dehashed version of 'in'?
            if (!dehashed.empty()) { dehashed += "__DOT__"; }
            last_dot_pos = next_dot_pos + DOT_LEN;
        } else {
            last_dot_pos = string::npos;
        }
    }
    return dehashed.empty() ? in : dehashed;
}

string VName::hashedName() {
    if (m_name == "") return "";
    if (m_hashed != "") return m_hashed;  // Memoized
    if (s_maxLength == 0 || m_name.length() < s_maxLength) {
        m_hashed = m_name;
        return m_hashed;
    } else {
        VHashSha256 hash(m_name);
        const string suffix = "__Vhsh" + hash.digestSymbol();
        if (s_minLength < s_maxLength) {
            s_dehashMap[suffix] = m_name.substr(s_minLength);
            m_hashed = m_name.substr(0, s_minLength) + suffix;
        } else {
            s_dehashMap[suffix] = m_name;
            m_hashed = suffix;
        }
        return m_hashed;
    }
}

//######################################################################
// VSpellCheck - Algorithm same as GCC's spellcheck.c

VSpellCheck::EditDistance VSpellCheck::editDistance(const string& s, const string& t) {
    // Wagner-Fischer algorithm for the Damerau-Levenshtein distance
    const size_t sLen = s.length();
    const size_t tLen = t.length();
    if (sLen == 0) return tLen;
    if (tLen == 0) return sLen;
    if (sLen >= LENGTH_LIMIT) return sLen;
    if (tLen >= LENGTH_LIMIT) return tLen;

    static std::array<EditDistance, LENGTH_LIMIT + 1> s_v_two_ago;
    static std::array<EditDistance, LENGTH_LIMIT + 1> s_v_one_ago;
    static std::array<EditDistance, LENGTH_LIMIT + 1> s_v_next;

    for (size_t i = 0; i < sLen + 1; i++) s_v_one_ago[i] = i;

    for (size_t i = 0; i < tLen; i++) {
        s_v_next[0] = i + 1;
        for (size_t j = 0; j < sLen; j++) {
            const EditDistance cost = (s[j] == t[i] ? 0 : 1);
            const EditDistance deletion = s_v_next[j] + 1;
            const EditDistance insertion = s_v_one_ago[j + 1] + 1;
            const EditDistance substitution = s_v_one_ago[j] + cost;
            EditDistance cheapest = std::min(deletion, insertion);
            cheapest = std::min(cheapest, substitution);
            if (i > 0 && j > 0 && s[j] == t[i - 1] && s[j - 1] == t[i]) {
                const EditDistance transposition = s_v_two_ago[j - 1] + 1;
                cheapest = std::min(cheapest, transposition);
            }
            s_v_next[j + 1] = cheapest;
        }
        for (size_t j = 0; j < sLen + 1; j++) {
            s_v_two_ago[j] = s_v_one_ago[j];
            s_v_one_ago[j] = s_v_next[j];
        }
    }

    const EditDistance result = s_v_next[sLen];
    return result;
}

VSpellCheck::EditDistance VSpellCheck::cutoffDistance(size_t goal_len, size_t candidate_len) {
    // Return max acceptable edit distance
    const size_t max_length = std::max(goal_len, candidate_len);
    const size_t min_length = std::min(goal_len, candidate_len);
    if (max_length <= 1) return 0;
    if (max_length - min_length <= 1) return std::max(max_length / 3, static_cast<size_t>(1));
    return (max_length + 2) / 3;
}

string VSpellCheck::bestCandidateInfo(const string& goal, EditDistance& distancer) const {
    string bestCandidate;
    const size_t gLen = goal.length();
    distancer = LENGTH_LIMIT * 10;
    for (const string& candidate : m_candidates) {
        const size_t cLen = candidate.length();

        // Min distance must be inserting/deleting to make lengths match
        const EditDistance min_distance = (cLen > gLen ? (cLen - gLen) : (gLen - cLen));
        if (min_distance >= distancer) continue;  // Short-circuit if already better

        const EditDistance cutoff = cutoffDistance(gLen, cLen);
        if (min_distance > cutoff) continue;  // Short-circuit if already too bad

        const EditDistance dist = editDistance(goal, candidate);
        UINFO(9, "EditDistance dist=" << dist << " cutoff=" << cutoff << " goal=" << goal
                                      << " candidate=" << candidate << endl);
        if (dist < distancer && dist <= cutoff) {
            distancer = dist;
            bestCandidate = candidate;
        }
    }

    // If goal matches candidate avoid suggesting replacing with self
    if (distancer == 0) return "";
    return bestCandidate;
}

void VSpellCheck::selfTestDistanceOne(const string& a, const string& b, EditDistance expected) {
    UASSERT_SELFTEST(EditDistance, editDistance(a, b), expected);
    UASSERT_SELFTEST(EditDistance, editDistance(b, a), expected);
}

void VSpellCheck::selfTestSuggestOne(bool matches, const string& c, const string& goal,
                                     EditDistance dist) {
    EditDistance gdist;
    VSpellCheck speller;
    speller.pushCandidate(c);
    const string got = speller.bestCandidateInfo(goal, gdist /*ref*/);
    if (matches) {
        UASSERT_SELFTEST(const string&, got, c);
        UASSERT_SELFTEST(EditDistance, gdist, dist);
    } else {
        UASSERT_SELFTEST(const string&, got, "");
    }
}

void VSpellCheck::selfTest() {
    {
        selfTestDistanceOne("ab", "ac", 1);
        selfTestDistanceOne("ab", "a", 1);
        selfTestDistanceOne("a", "b", 1);
    }
    {
        selfTestSuggestOne(true, "DEL_ETE", "DELETE", 1);
        selfTestSuggestOne(true, "abcdef", "acbdef", 1);
        selfTestSuggestOne(true, "db", "dc", 1);
        selfTestSuggestOne(true, "db", "dba", 1);
        // Negative suggestions
        selfTestSuggestOne(false, "x", "y", 1);
        selfTestSuggestOne(false, "sqrt", "assert", 3);
    }
    {
        const VSpellCheck speller;
        UASSERT_SELFTEST(string, "", speller.bestCandidate(""));
    }
    {
        VSpellCheck speller;
        speller.pushCandidate("fred");
        speller.pushCandidate("wilma");
        speller.pushCandidate("barney");
        UASSERT_SELFTEST(string, "fred", speller.bestCandidate("fre"));
        UASSERT_SELFTEST(string, "wilma", speller.bestCandidate("whilma"));
        UASSERT_SELFTEST(string, "barney", speller.bestCandidate("Barney"));
        UASSERT_SELFTEST(string, "", speller.bestCandidate("nothing close"));
    }
}
