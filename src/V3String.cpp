// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Options parsing
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#if defined(_WIN32) || defined(__MINGW32__)
#include <io.h>  // open, read, write, close
#endif

#include "V3Error.h"
#include "V3FileLine.h"
#include "V3String.h"

#ifndef V3ERROR_NO_GLOBAL_
#include "V3Global.h"
VL_DEFINE_DEBUG_FUNCTIONS;
#endif

#include <algorithm>
#include <fcntl.h>

size_t VName::s_minLength = 32;
size_t VName::s_maxLength = 0;  // Disabled
std::map<string, string> VName::s_dehashMap;

//######################################################################
// Wildcard

// Double procedures, inlined, unrolls loop much better
template <bool Even = true>
static bool wildMatchImpl(const char* s, const char* p) VL_PURE {
    for (; *p; s++, p++) {
        if (*p != '*') {
            if (((*s) != (*p)) && *p != '?') return false;
        } else {
            // Trailing star matches everything.
            if (!*++p) return true;
            while (!wildMatchImpl<!Even>(s, p)) {
                if (*++s == '\0') return false;
            }
            return true;
        }
    }
    return (*s == '\0');
}

bool VString::wildmatch(const char* s, const char* p) VL_PURE {
    if (*s == '\0') {
        while (*p == '*') ++p;
        return *p == '\0';
    }
    return wildMatchImpl(s, p);
}

bool VString::wildmatch(const string& s, const string& p) VL_PURE {
    return wildmatch(s.c_str(), p.c_str());
}

string VString::dot(const string& a, const string& dot, const string& b) {
    if (b == "") return a;
    if (a == "") return b;
    return a + dot + b;
}

string VString::downcase(const string& str) VL_PURE {
    string result = str;
    for (char& cr : result) cr = std::tolower(cr);
    return result;
}

string VString::upcase(const string& str) VL_PURE {
    string result = str;
    for (char& cr : result) cr = std::toupper(cr);
    return result;
}

string VString::quoteAny(const string& str, char tgt, char esc) VL_PURE {
    string result;
    for (const char c : str) {
        if (c == tgt) result += esc;
        result += c;
    }
    return result;
}

string VString::dequotePercent(const string& str) {
    string result;
    char last = '\0';
    for (const char c : str) {
        if (last == '%' && c == '%') {
            last = '\0';
        } else {
            result += c;
            last = c;
        }
    }
    return result;
}

string VString::quoteStringLiteralForShell(const string& str) {
    string result;
    constexpr char dquote = '"';
    constexpr char escape = '\\';
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

string VString::escapeStringForPath(const string& str) {
    if (str.find(R"(\\)") != string::npos)
        return str;  // if it has been escaped already, don't do it again
    if (str.find('/') != string::npos) return str;  // can be replaced by `__MINGW32__` or `_WIN32`
    string result;
    constexpr char space = ' ';  // escape space like this `Program Files`
    constexpr char escape = '\\';
    for (const char c : str) {
        if (c == space || c == escape) result.push_back(escape);
        result.push_back(c);
    }
    return result;
}

static int vl_decodexdigit(char c) {
    return std::isdigit(c) ? c - '0' : std::tolower(c) - 'a' + 10;
}

string VString::unquoteSVString(const string& text, string& errOut) {
    bool quoted = false;
    string newtext;
    newtext.reserve(text.size());
    unsigned char octal_val = 0;
    int octal_digits = 0;
    for (string::const_iterator cp = text.begin(); cp != text.end(); ++cp) {
        if (quoted) {
            if (std::isdigit(*cp)) {
                octal_val = octal_val * 8 + (*cp - '0');
                if (++octal_digits == 3) {
                    newtext += octal_val;
                    octal_digits = 0;
                    octal_val = 0;
                    quoted = false;
                }
            } else {
                if (octal_digits) {
                    // Spec allows 1-3 digits
                    newtext += octal_val;
                    octal_digits = 0;
                    octal_val = 0;
                    quoted = false;
                    --cp;  // Backup to reprocess terminating character as non-escaped
                    continue;
                }
                quoted = false;
                if (*cp == 'n') {
                    newtext += '\n';
                } else if (*cp == 'a') {
                    newtext += '\a';  // SystemVerilog 3.1
                } else if (*cp == 'f') {
                    newtext += '\f';  // SystemVerilog 3.1
                } else if (*cp == 'r') {
                    newtext += '\r';
                } else if (*cp == 't') {
                    newtext += '\t';
                } else if (*cp == 'v') {
                    newtext += '\v';  // SystemVerilog 3.1
                } else if (*cp == 'x' && std::isxdigit(cp[1])
                           && std::isxdigit(cp[2])) {  // SystemVerilog 3.1
                    newtext
                        += static_cast<char>(16 * vl_decodexdigit(cp[1]) + vl_decodexdigit(cp[2]));
                    cp += 2;
                } else if (std::isalnum(*cp)) {
                    errOut = "Unknown escape sequence: \\";
                    errOut += *cp;
                    break;
                } else {
                    newtext += *cp;
                }
            }
        } else if (*cp == '\\') {
            if (octal_digits) {
                newtext += octal_val;
                // below: octal_digits = 0;
                octal_val = 0;
            }
            quoted = true;
            octal_digits = 0;
        } else {
            newtext += *cp;
        }
    }
    return newtext;
}

size_t VString::quotedEnd(const string& str, size_t pos) VL_PURE {
    for (size_t i = pos + 1; i < str.size(); ++i) {
        if (str[i] == '\\') {
            ++i;  // Past the escaped character, as of '\"'
        } else if (str[i] == '"') {
            return i + 1;
        }
    }
    return string::npos;
}

string VString::spaceUnprintable(const string& str) VL_PURE {
    string result;
    for (const char c : str) {
        if (std::isprint(c)) {
            result += c;
        } else {
            result += ' ';
        }
    }
    return result;
}

string VString::removeWhitespace(const string& str) {
    string result;
    result.reserve(str.size());
    for (const char c : str) {
        if (!std::isspace(c)) result += c;
    }
    return result;
}

string VString::trimWhitespace(const string& str) {
    string result;
    result.reserve(str.size());
    string add;
    bool newline = false;
    for (const char c : str) {
        if (newline && std::isspace(c)) continue;
        if (c == '\n') {
            add = "\n";
            newline = true;
            continue;
        }
        if (std::isspace(c)) {
            add += c;
            continue;
        }
        if (!add.empty()) {
            result += add;
            newline = false;
            add.clear();
        }
        result += c;
    }
    return result;
}

bool VString::isIdentifier(const string& str) {
    for (const char c : str) {
        if (!isIdentifierChar(c)) return false;
    }
    return true;
}

bool VString::isWhitespace(const string& str) {
    for (const char c : str) {
        if (!std::isspace(c)) return false;
    }
    return true;
}

string::size_type VString::leadingWhitespaceCount(const string& str) {
    string::size_type result = 0;
    for (const char c : str) {
        ++result;
        if (!std::isspace(c)) break;
    }
    return result;
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
    if (parsed_len != std::strlen(strgp)) {
        if (successp) *successp = false;
    }
    VL_DO_DANGLING(delete[] strgp, strgp);
    return d;
}

string VString::replaceSubstr(const string& str, const string& from, const string& to) {
    string result = str;
    const size_t fromLen = from.size();
    const size_t toLen = to.size();
    UASSERT_STATIC(fromLen > 0, "Cannot replace empty string");
    for (size_t pos = 0; (pos = result.find(from, pos)) != string::npos; pos += toLen) {
        result.replace(pos, fromLen, to);
    }
    return result;
}

string VString::replaceWord(const string& str, const string& from, const string& to) {
    string result = str;
    const size_t len = from.size();
    UASSERT_STATIC(len > 0, "Cannot replace empty string");
    for (size_t pos = 0; (pos = result.find(from, pos)) != string::npos; pos += len) {
        // Only replace whole words
        if (((pos > 0) && VString::isIdentifierChar(result[pos - 1])) ||  //
            ((pos + len < result.size()) && VString::isIdentifierChar(result[pos + len]))) {
            continue;
        }
        result.replace(pos, len, to);
    }
    return result;
}

std::deque<string> VString::split(const string& str, char delimiter) {
    std::deque<std::string> results;
    std::istringstream is{str};
    std::string token;
    while (std::getline(is, token, delimiter)) results.push_back(token);
    return results;
}

bool VString::endsWith(const string& str, const string& suffix) {
    if (str.length() < suffix.length()) return false;
    return str.compare(str.length() - suffix.length(), suffix.length(), suffix) == 0;
}
string VString::aOrAn(const char* word) {
    switch (word[0]) {
    case '\0': return "";
    case 'a':
    case 'e':
    case 'i':
    case 'o':
    case 'u': return "an";
    default: return "a";
    }
}

// MurmurHash64A
uint64_t VString::hashMurmur(const string& str) VL_PURE {
    const char* key = str.c_str();
    const size_t len = str.size();
    constexpr uint64_t seed = 0;
    constexpr uint64_t m = 0xc6a4a7935bd1e995ULL;
    constexpr int r = 47;

    uint64_t h = seed ^ (len * m);

    const uint64_t* data = reinterpret_cast<const uint64_t*>(key);
    const uint64_t* end = data + (len / 8);

    while (data != end) {
        uint64_t k = *data++;

        k *= m;
        k ^= k >> r;
        k *= m;

        h ^= k;
        h *= m;
    }

    const unsigned char* data2 = reinterpret_cast<const unsigned char*>(data);

    switch (len & 7) {
    case 7: h ^= static_cast<uint64_t>(data2[6]) << 48;  // FALLTHRU
    case 6: h ^= static_cast<uint64_t>(data2[5]) << 40;  // FALLTHRU
    case 5: h ^= static_cast<uint64_t>(data2[4]) << 32;  // FALLTHRU
    case 4: h ^= static_cast<uint64_t>(data2[3]) << 24;  // FALLTHRU
    case 3: h ^= static_cast<uint64_t>(data2[2]) << 16;  // FALLTHRU
    case 2: h ^= static_cast<uint64_t>(data2[1]) << 8;  // FALLTHRU
    case 1: h ^= static_cast<uint64_t>(data2[0]); h *= m;  // FALLTHRU
    default:;
    };

    h ^= h >> r;
    h *= m;
    h ^= h >> r;

    return h;
}

string VString::base64Enc(const string& str) VL_PURE {
    // Non-URL format (+/), versus URL format (-/).
    static constexpr const char* const digits
        = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    size_t len = str.size();
    string result;
    result.reserve(len * 4 / 3 + 2);
    size_t pos = 0;
    if (len >= 3) {
        for (; pos < len - 2; pos += 3) {
            result += digits[((str[pos] >> 2) & 0x3f)];
            result
                += digits[((str[pos] & 0x3) << 4) | (static_cast<int>(str[pos + 1] & 0xf0) >> 4)];
            result += digits[((str[pos + 1] & 0xf) << 2)
                             | (static_cast<int>(str[pos + 2] & 0xc0) >> 6)];
            result += digits[((str[pos + 2] & 0x3f))];
        }
    }
    if (len >= 2 && pos < len - 1) {  // Pad 2
        result += digits[((str[pos] >> 2) & 0x3f)];
        result += digits[((str[pos] & 0x3) << 4) | (static_cast<int>(str[pos + 1] & 0xf0) >> 4)];
        result += digits[((str[pos + 1] & 0xf) << 2) | (static_cast<int>(0) >> 6)];
        result += '=';
    } else if (pos < len) {  // Pad 1
        result += digits[((str[pos] >> 2) & 0x3f)];
        result += digits[((str[pos] & 0x3) << 4) | (static_cast<int>(0) >> 4)];
        result += '=';
        result += '=';
    }
    return result;
}

void VString::selfTest() {
    UASSERT_SELFTEST(VString::replaceSubstr("aa", "a", "ba"), "baba");

    // Cross-checked with 'base64'
    UASSERT_SELFTEST(VString::base64Enc(""), "");
    UASSERT_SELFTEST(VString::base64Enc("x"), "eA==");
    UASSERT_SELFTEST(VString::base64Enc("xy"), "eHk=");
    UASSERT_SELFTEST(VString::base64Enc("xyz"), "eHl6");
    UASSERT_SELFTEST(
        VString::base64Enc("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/~"),
        "QUJDREVGR0hJSktMTU5PUFFSU1RVVldYWVphYmNkZWZnaGlqa2xtbm9wcXJzdHV2d3h5ejAxM"
        "jM0NTY3ODkrL34=");
}

//######################################################################
// VHashSha512

static constexpr uint64_t sha512K[]
    = {0x428a2f98d728ae22ULL, 0x7137449123ef65cdULL, 0xb5c0fbcfec4d3b2fULL, 0xe9b5dba58189dbbcULL,
       0x3956c25bf348b538ULL, 0x59f111f1b605d019ULL, 0x923f82a4af194f9bULL, 0xab1c5ed5da6d8118ULL,
       0xd807aa98a3030242ULL, 0x12835b0145706fbeULL, 0x243185be4ee4b28cULL, 0x550c7dc3d5ffb4e2ULL,
       0x72be5d74f27b896fULL, 0x80deb1fe3b1696b1ULL, 0x9bdc06a725c71235ULL, 0xc19bf174cf692694ULL,
       0xe49b69c19ef14ad2ULL, 0xefbe4786384f25e3ULL, 0x0fc19dc68b8cd5b5ULL, 0x240ca1cc77ac9c65ULL,
       0x2de92c6f592b0275ULL, 0x4a7484aa6ea6e483ULL, 0x5cb0a9dcbd41fbd4ULL, 0x76f988da831153b5ULL,
       0x983e5152ee66dfabULL, 0xa831c66d2db43210ULL, 0xb00327c898fb213fULL, 0xbf597fc7beef0ee4ULL,
       0xc6e00bf33da88fc2ULL, 0xd5a79147930aa725ULL, 0x06ca6351e003826fULL, 0x142929670a0e6e70ULL,
       0x27b70a8546d22ffcULL, 0x2e1b21385c26c926ULL, 0x4d2c6dfc5ac42aedULL, 0x53380d139d95b3dfULL,
       0x650a73548baf63deULL, 0x766a0abb3c77b2a8ULL, 0x81c2c92e47edaee6ULL, 0x92722c851482353bULL,
       0xa2bfe8a14cf10364ULL, 0xa81a664bbc423001ULL, 0xc24b8b70d0f89791ULL, 0xc76c51a30654be30ULL,
       0xd192e819d6ef5218ULL, 0xd69906245565a910ULL, 0xf40e35855771202aULL, 0x106aa07032bbd1b8ULL,
       0x19a4c116b8d2d0c8ULL, 0x1e376c085141ab53ULL, 0x2748774cdf8eeb99ULL, 0x34b0bcb5e19b48a8ULL,
       0x391c0cb3c5c95a63ULL, 0x4ed8aa4ae3418acbULL, 0x5b9cca4f7763e373ULL, 0x682e6ff3d6b2b8a3ULL,
       0x748f82ee5defb2fcULL, 0x78a5636f43172f60ULL, 0x84c87814a1f0ab72ULL, 0x8cc702081a6439ecULL,
       0x90befffa23631e28ULL, 0xa4506cebde82bde9ULL, 0xbef9a3f7b2c67915ULL, 0xc67178f2e372532bULL,
       0xca273eceea26619cULL, 0xd186b8c721c0c207ULL, 0xeada7dd6cde0eb1eULL, 0xf57d4f7fee6ed178ULL,
       0x06f067aa72176fbaULL, 0x0a637dc5a2c898a6ULL, 0x113f9804bef90daeULL, 0x1b710b35131c471bULL,
       0x28db77f523047d84ULL, 0x32caab7b40c72493ULL, 0x3c9ebe0a15c9bebcULL, 0x431d67c49c100d4cULL,
       0x4cc5d4becb3e42b6ULL, 0x597f299cfc657e2aULL, 0x5fcb6fab3ad6faecULL, 0x6c44198c4a475817ULL};

VL_ATTR_ALWINLINE
static uint64_t shaRotr64(uint64_t lhs, uint64_t rhs) VL_PURE {
    return lhs >> rhs | lhs << (64 - rhs);
}

VL_ATTR_ALWINLINE
static void sha512Block(uint64_t* h, const uint64_t* chunk) VL_PURE {
    uint64_t ah[8];
    const uint64_t* p = chunk;

    // Initialize working variables to current hash value
    for (unsigned i = 0; i < 8; i++) ah[i] = h[i];
    // Compression function main loop
    uint64_t w[16] = {};
    for (unsigned i = 0; i < 5; ++i) {
        for (unsigned j = 0; j < 16; ++j) {
            if (i == 0) {
                w[j] = *p++;
            } else {
                // Extend the first 16 words into the remaining
                // 64 words w[16..79] of the message schedule array:
                const uint64_t s0 = shaRotr64(w[(j + 1) & 0xf], 1) ^ shaRotr64(w[(j + 1) & 0xf], 8)
                                    ^ (w[(j + 1) & 0xf] >> 7);
                const uint64_t s1 = shaRotr64(w[(j + 14) & 0xf], 19)
                                    ^ shaRotr64(w[(j + 14) & 0xf], 61) ^ (w[(j + 14) & 0xf] >> 6);
                w[j] = w[j] + s0 + w[(j + 9) & 0xf] + s1;
            }
            const uint64_t s1 = shaRotr64(ah[4], 14) ^ shaRotr64(ah[4], 18) ^ shaRotr64(ah[4], 41);
            const uint64_t ch = (ah[4] & ah[5]) ^ (~ah[4] & ah[6]);
            const uint64_t temp1 = ah[7] + s1 + ch + sha512K[i * 16 + j] + w[j];
            const uint64_t s0 = shaRotr64(ah[0], 28) ^ shaRotr64(ah[0], 34) ^ shaRotr64(ah[0], 39);
            const uint64_t maj = (ah[0] & ah[1]) ^ (ah[0] & ah[2]) ^ (ah[1] & ah[2]);
            const uint64_t temp2 = s0 + maj;

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

void VHashSha512::insert(const void* datap, size_t length) {
    UASSERT(!m_final, "Called VHashSha512::insert after finalized the hash value");
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
        tempData = m_remainder + std::string{static_cast<const char*>(datap), length};
        chunkLen = tempData.length();
        chunkp = reinterpret_cast<const uint8_t*>(tempData.data());
    }

    // See wikipedia SHA-2 algorithm summary
    uint64_t w[80];  // Round buffer, [0..15] are input data, rest used by rounds
    int posBegin = 0;  // Position in buffer for start of this block
    int posEnd = 0;  // Position in buffer for end of this block

    // Process complete 128-byte blocks
    while (posBegin <= chunkLen - 128) {
        posEnd = posBegin + 128;
        // 128 byte round input data, being careful to swap on big, keep on little
        for (int roundByte = 0; posBegin < posEnd; posBegin += 8) {
            w[roundByte++] = (static_cast<uint64_t>(chunkp[posBegin + 7])
                              | (static_cast<uint64_t>(chunkp[posBegin + 6]) << 8)
                              | (static_cast<uint64_t>(chunkp[posBegin + 5]) << 16)
                              | (static_cast<uint64_t>(chunkp[posBegin + 4]) << 24)
                              | (static_cast<uint64_t>(chunkp[posBegin + 3]) << 32)
                              | (static_cast<uint64_t>(chunkp[posBegin + 2]) << 40)
                              | (static_cast<uint64_t>(chunkp[posBegin + 1]) << 48)
                              | (static_cast<uint64_t>(chunkp[posBegin]) << 56));
        }
        sha512Block(m_inthash, w);
    }

    m_remainder = std::string(reinterpret_cast<const char*>(chunkp + posBegin), chunkLen - posEnd);
}

void VHashSha512::insertFile(const string& filename) {
    static constexpr size_t BUFFER_SIZE = 64 * 1024;

    const int fd = ::open(filename.c_str(), O_RDONLY);
    if (fd < 0) return;

    std::array<char, BUFFER_SIZE + 1> buf;
    while (const ssize_t got = ::read(fd, &buf, BUFFER_SIZE)) {
        if (got <= 0) break;
        insert(&buf, got);
    }
    ::close(fd);
}

void VHashSha512::finalize() {
    if (!m_final) {
        // Make sure no 128 byte blocks left
        insert("");
        m_final = true;

        // Process final possibly non-complete 128-byte block
        uint64_t w[16];  // Round buffer, [0..15] are input data
        for (int i = 0; i < 16; ++i) w[i] = 0;
        size_t blockPos = 0;
        for (; blockPos < m_remainder.length(); ++blockPos) {
            w[blockPos >> 3]
                |= ((static_cast<uint64_t>(static_cast<uint8_t>(m_remainder[blockPos])))
                    << ((7 - (blockPos & 7)) << 3));
        }
        w[blockPos >> 3] |= static_cast<uint64_t>(0x80) << ((7 - (blockPos & 7)) << 3);
        if (m_remainder.length() >= 112) {
            sha512Block(m_inthash, w);
            for (int i = 0; i < 16; ++i) w[i] = 0;
        }
        // Only supporting 2^61 bytes max
        w[14] = 0;
        w[15] = m_totLength << 3;
        sha512Block(m_inthash, w);

        m_remainder.clear();
    }
}

string VHashSha512::digestBinary() {
    finalize();
    string result;
    result.reserve(64);
    for (size_t i = 0; i < 64; ++i) {
        result += static_cast<char>((m_inthash[i >> 3] >> (((7 - i) & 0x7) << 3)) & 0xff);
    }
    return result;
}

uint64_t VHashSha512::digestUInt64() {
    const string& binhash = digestBinary();
    uint64_t result = 0;
    for (size_t byte = 0; byte < sizeof(uint64_t); ++byte) {
        const unsigned char c = binhash[byte];
        result = (result << 8) | c;
    }
    return result;
}

string VHashSha512::digestHex() {
    static constexpr const char* const digits = "0123456789abcdef";
    const string& binhash = digestBinary();
    string result;
    result.reserve(128);
    for (size_t byte = 0; byte < 64; ++byte) {
        result += digits[(binhash[byte] >> 4) & 0xf];
        result += digits[(binhash[byte] >> 0) & 0xf];
    }
    return result;
}

string VHashSha512::digestBase64() {
    // Return base64 from hash.  Complete representation of the binary/reversable.
    return VString::base64Enc(digestBinary());
}

string VHashSha512::digestSymbol24() {
    // Make a symbol name from hash.  Similar to base64, however base 64
    // has + and / for last two digits, but need C symbol, and we also
    // avoid conflicts with use of _, so use "AB" at the end.
    // Thus this function is non-reversible.
    static constexpr const char* const digits
        = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789AB";
    const string& binhash = digestBinary();
    string result;
    result.reserve(84);
    int pos = 0;
    for (; pos < (512 / 8) - 2; pos += 3) {
        result += digits[((binhash[pos] >> 2) & 0x3f)];
        result += digits[((binhash[pos] & 0x3) << 4)
                         | (static_cast<int>(binhash[pos + 1] & 0xf0) >> 4)];
        result += digits[((binhash[pos + 1] & 0xf) << 2)
                         | (static_cast<int>(binhash[pos + 2] & 0xc0) >> 6)];
        result += digits[((binhash[pos + 2] & 0x3f))];
        // Keep symbols short-ish, with 24 chars/144 bits we won't have hash collisions
        if (result.size() >= DIGEST_SYMBOL24_LENGTH) break;
    }
    // Any leftover bits don't matter for our purpose
    return result;
}

void VHashSha512::selfTestOne(const string& data, const string& data2, const string& exp,
                              const string& exp64, const string& exp24) {
    VHashSha512 digest{data};
    if (data2 != "") digest.insert(data2);
    if (VL_UNCOVERABLE(digest.digestHex() != exp)) {
        std::cerr << "%Error: When hashing '" << data + data2 << "'\n"  // LCOV_EXCL_LINE
                  << "        ... got=" << digest.digestHex() << '\n'  // LCOV_EXCL_LINE
                  << "        ... exp=" << exp << endl;  // LCOV_EXCL_LINE
    }
    if (VL_UNCOVERABLE(digest.digestBase64() != exp64)) {
        std::cerr << "%Error: When hashing '" << data + data2 << "'\n"  // LCOV_EXCL_LINE
                  << "        ... got=" << digest.digestBase64() << '\n'  // LCOV_EXCL_LINE
                  << "        ... exp=" << exp64 << endl;  // LCOV_EXCL_LINE
    }
    if (VL_UNCOVERABLE(digest.digestSymbol24() != exp24)) {
        std::cerr << "%Error: When hashing '" << data + data2 << "'\n"  // LCOV_EXCL_LINE
                  << "        ... got=" << digest.digestSymbol24() << '\n'  // LCOV_EXCL_LINE
                  << "        ... exp=" << exp64 << endl;  // LCOV_EXCL_LINE
    }
}

void VHashSha512::selfTest() {
    // Cross-checked with sha512sum
    selfTestOne(
        "", "",
        "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce"
        "47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e",
        "z4PhNX7vuL3xVChQ1m2AB9Yg5AULVxXcg/SpIdNs6c5H0NE8XYXysP+DGNKHfuwvY7kxvUdBeoGlODJ6+SfaPg==",
        "z4PhNX7vuL3xVChQ1m2AB9Yg");
    selfTestOne(
        "a", "",
        "1f40fc92da241694750979ee6cf582f2d5d7d28e18335de05abc54d0560e0f53"
        "02860c652bf08d560252aa5e74210546f369fbbbce8c12cfc7957b2652fe9a75",
        "H0D8ktokFpR1CXnubPWC8tXX0o4YM13gWrxU0FYOD1MChgxlK/CNVgJSql50IQVG82n7u86MEs/HlXsmUv6adQ==",
        "H0D8ktokFpR1CXnubPWC8tXX");
    selfTestOne(
        "The quick brown fox jumps over the lazy dog", "",
        "07e547d9586f6a73f73fbac0435ed76951218fb7d0c8d788a309d785436bbb64"
        "2e93a252a954f23912547d1e8a3b5ed6e1bfd7097821233fa0538f3db854fee6",
        "B+VH2VhvanP3P7rAQ17XaVEhj7fQyNeIownXhUNru2Quk6JSqVTyORJUfR6KO17W4b/XCXghIz+gU489uFT+5g==",
        "BAVH2VhvanP3P7rAQ17XaVEh");
    selfTestOne(
        "The quick brown fox jumps over the lazy", " dog",
        "07e547d9586f6a73f73fbac0435ed76951218fb7d0c8d788a309d785436bbb64"
        "2e93a252a954f23912547d1e8a3b5ed6e1bfd7097821233fa0538f3db854fee6",
        "B+VH2VhvanP3P7rAQ17XaVEhj7fQyNeIownXhUNru2Quk6JSqVTyORJUfR6KO17W4b/XCXghIz+gU489uFT+5g==",
        "BAVH2VhvanP3P7rAQ17XaVEh");
    selfTestOne(
        "Test using larger than block-size key and larger than one block-size data."
        " SHA512 has a 128 byte block size so this needs to be more than 128 characters long.",
        "",
        "6f51a6ddad3a86fccd8d1d6584712567ee60b00d6d31bfecb69b0e288f45fbbd"
        "91b785c218f1e7c019088ad9f47680a93720bada029294dd7a7fb8119137dbf1",
        "b1Gm3a06hvzNjR1lhHElZ+5gsA1tMb/stpsOKI9F+72Rt4XCGPHnwBkIitn0doCpNyC62gKSlN16f7gRkTfb8Q==",
        "b1Gm3a06hvzNjR1lhHElZA5g");
    selfTestOne(
        "Test using",
        " larger than block-size key and larger than one block-size data."
        " SHA512 has a 128 byte block size so this needs to be more than 128 characters long.",
        "6f51a6ddad3a86fccd8d1d6584712567ee60b00d6d31bfecb69b0e288f45fbbd"
        "91b785c218f1e7c019088ad9f47680a93720bada029294dd7a7fb8119137dbf1",
        "b1Gm3a06hvzNjR1lhHElZ+5gsA1tMb/stpsOKI9F+72Rt4XCGPHnwBkIitn0doCpNyC62gKSlN16f7gRkTfb8Q==",
        "b1Gm3a06hvzNjR1lhHElZA5g");
}

//######################################################################
// VName

string VName::dehash(const string& in) {
    static constexpr const char VHSH[] = "__Vhsh";
    static constexpr size_t VHSH_LEN = sizeof(VHSH) - 1 + VHashSha512::DIGEST_SYMBOL24_LENGTH;
    static const size_t DOT_LEN = std::strlen("__DOT__");
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
            // V3SplitVar appends a bit range to a name hashedName already hashed, so the
            // hash does not always reach the end of the component.
            const auto end_vhsh
                = begin_vhsh + std::min<size_t>(std::distance(begin_vhsh, search_end), VHSH_LEN);
            const std::string vhsh{begin_vhsh, end_vhsh};
            const auto& it = s_dehashMap.find(vhsh);
            UASSERT(it != s_dehashMap.end(), "String not in reverse hash map '" << vhsh << "'");
            // Is this not the first component, but the first to require dehashing?
            if (last_dot_pos > 0 && dehashed.empty()) {
                // Seed 'dehashed' with the previously processed components.
                dehashed = in.substr(0, last_dot_pos);
            }
            // Append the unhashed part of the component.
            dehashed += std::string{search_begin, begin_vhsh};
            // Append the bit that was lost to truncation but retrieved from the dehash map.
            dehashed += it->second;
            // Append what follows the hash, such as a split variable bit range.
            dehashed += std::string{end_vhsh, search_end};
        }
        // This component doesn't need dehashing but a previous one might have.
        else if (!dehashed.empty()) {
            dehashed += std::string{search_begin, search_end};
        }

        if (next_dot_pos != string::npos) {
            // Is there a __DOT__ to add to the dehashed version of 'in'?
            if (!dehashed.empty()) dehashed += "__DOT__";
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
    }
    VHashSha512 hash{m_name};
    const string suffix = "__Vhsh" + hash.digestSymbol24();
    if (s_minLength < s_maxLength) {
        // Keep a prefix from the original name
        // Backup over digits so adding __Vhash doesn't look like a encoded hex digit
        // ("__0__Vhsh")
        size_t prefLength = s_minLength;
        while (prefLength >= 1 && m_name[prefLength - 1] != '_') --prefLength;
        s_dehashMap[suffix] = m_name.substr(prefLength);
        m_hashed = m_name.substr(0, prefLength) + suffix;
    } else {
        s_dehashMap[suffix] = m_name;
        m_hashed = suffix;
    }
    return m_hashed;
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
    string best;
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
                                      << " candidate=" << candidate);
        if (dist < distancer && dist <= cutoff) {
            distancer = dist;
            best = candidate;
        }
    }

    // If goal matches candidate avoid suggesting replacing with self
    if (distancer == 0) return "";
    return best;
}

void VSpellCheck::selfTestDistanceOne(const string& a, const string& b, EditDistance expected) {
    UASSERT_SELFTEST(editDistance(a, b), expected);
    UASSERT_SELFTEST(editDistance(b, a), expected);
}

void VSpellCheck::selfTestSuggestOne(bool matches, const string& c, const string& goal,
                                     EditDistance dist) {
    EditDistance gdist;
    VSpellCheck speller;
    speller.pushCandidate(c);
    const string got = speller.bestCandidateInfo(goal, gdist /*ref*/);
    if (matches) {
        UASSERT_SELFTEST(got, c);
        UASSERT_SELFTEST(gdist, dist);
    } else {
        UASSERT_SELFTEST(got, "");
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
        UASSERT_SELFTEST(speller.bestCandidate(""), "");
    }
    {
        VSpellCheck speller;
        speller.pushCandidate("fred");
        speller.pushCandidate("wilma");
        speller.pushCandidate("barney");
        UASSERT_SELFTEST(speller.bestCandidate("fre"), "fred");
        UASSERT_SELFTEST(speller.bestCandidate("whilma"), "wilma");
        UASSERT_SELFTEST(speller.bestCandidate("Barney"), "barney");
        UASSERT_SELFTEST(speller.bestCandidate("nothing close"), "");
    }
}
