// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Bucket container
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

#ifndef VERILATOR_VLCBUCKET_H_
#define VERILATOR_VLCBUCKET_H_

#include "config_build.h"
#include "verilatedos.h"

#define V3ERROR_NO_GLOBAL_
#include "V3Error.h"

//********************************************************************
// VlcBuckets - Container of all coverage point hits for a given test
// This is a bitmap array - we store a single bit to indicate a test
// has hit that point with sufficient coverage.

class VlcBuckets final {
private:
    // MEMBERS
    uint64_t* m_datap = nullptr;  ///< Pointer to first bucket (dynamically allocated)
    uint64_t m_dataSize = 0;  ///< Current entries in m_datap
    uint64_t m_bucketsCovered = 0;  ///< Num buckets with sufficient coverage

    static uint64_t covBit(uint64_t point) { return 1ULL << (point & 63); }
    uint64_t allocSize() const { return sizeof(uint64_t) * m_dataSize / 64; }
    void allocate(uint64_t point) {
        const uint64_t oldsize = m_dataSize;
        if (m_dataSize < point) m_dataSize = (point + 64) & ~63ULL;  // Keep power of two
        m_dataSize *= 2;
        // UINFO(9, "Realloc "<<allocSize()<<" for "<<point<<"  "<<cvtToHex(m_datap)<<endl);
        uint64_t* const newp = static_cast<uint64_t*>(std::realloc(m_datap, allocSize()));
        if (VL_UNCOVERABLE(!newp)) {
            // cppcheck-suppress doubleFree  // cppcheck 1.90 bug - realloc doesn't free on fail
            free(m_datap);  // LCOV_EXCL_LINE
            v3fatal("Out of memory increasing buckets");  // LCOV_EXCL_LINE
        }
        m_datap = newp;
        for (uint64_t i = oldsize; i < m_dataSize; i += 64) m_datap[i / 64] = 0;
    }

public:
    // CONSTRUCTORS
    VlcBuckets() { allocate(1024); }
    ~VlcBuckets() {
        m_dataSize = 0;
        VL_DO_CLEAR(free(m_datap), m_datap = nullptr);
    }

    // ACCESSORS
    static uint64_t sufficient() { return 1; }
    uint64_t bucketsCovered() const { return m_bucketsCovered; }

    // METHODS
    void addData(uint64_t point, uint64_t hits) {
        if (hits >= sufficient()) {
            // UINFO(9,"     addData "<<point<<" "<<hits<<" size="<<m_dataSize<<endl);
            if (point >= m_dataSize) allocate(point);
            m_datap[point / 64] |= covBit(point);
            m_bucketsCovered++;
        }
    }
    void clearHits(uint64_t point) const {
        if (point >= m_dataSize) {
            return;
        } else {
            m_datap[point / 64] &= ~covBit(point);
        }
    }
    bool exists(uint64_t point) const {
        if (point >= m_dataSize) {
            return false;
        } else {
            return (m_datap[point / 64] & covBit(point)) ? 1 : 0;
        }
    }
    uint64_t hits(uint64_t point) const {
        if (point >= m_dataSize) {
            return 0;
        } else {
            return (m_datap[point / 64] & covBit(point)) ? 1 : 0;
        }
    }
    uint64_t popCount() const {
        uint64_t pop = 0;
        for (uint64_t i = 0; i < m_dataSize; ++i) {
            if (hits(i)) ++pop;
        }
        return pop;
    }
    uint64_t dataPopCount(const VlcBuckets& remaining) {
        uint64_t pop = 0;
        for (uint64_t i = 0; i < m_dataSize; ++i) {
            if (hits(i) && remaining.hits(i)) ++pop;
        }
        return pop;
    }
    void orData(const VlcBuckets& ordata) {
        for (uint64_t i = 0; i < m_dataSize; ++i) {
            if (hits(i) && ordata.hits(i)) clearHits(i);
        }
    }

    void dump() const {
        cout << "#     ";
        for (uint64_t i = 0; i < m_dataSize; i++) {
            if (hits(i)) cout << "," << i;
        }
        cout << endl;
    }
};

//######################################################################

#endif  // guard
