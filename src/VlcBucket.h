// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Bucket container
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

#ifndef _VLCBUCKET_H_
#define _VLCBUCKET_H_ 1

#include "config_build.h"
#include "verilatedos.h"

//********************************************************************
// VlcBuckets - Container of all coverage point hits for a given test
// This is a bitmap array - we store a single bit to indicate a test
// has hit that point with sufficient coverage.

class VlcBuckets {
private:
    // MEMBERS
    vluint64_t* m_datap;  ///< Pointer to first bucket (dynamically allocated)
    vluint64_t m_dataSize;  ///< Current entries in m_datap
    vluint64_t m_bucketsCovered;  ///< Num buckets with sufficient coverage

private:
    static inline vluint64_t covBit(vluint64_t point) { return 1ULL << (point & 63); }
    inline vluint64_t allocSize() const { return sizeof(vluint64_t) * m_dataSize / 64; }
    void allocate(vluint64_t point) {
        vluint64_t oldsize = m_dataSize;
        if (m_dataSize < point) m_dataSize = (point + 64) & ~63ULL;  // Keep power of two
        m_dataSize *= 2;
        // UINFO(9, "Realloc "<<allocSize()<<" for "<<point<<"  "<<cvtToHex(m_datap)<<endl);
        vluint64_t* newp = (vluint64_t*)realloc(m_datap, allocSize());
        if (!newp) {
            free(m_datap);
            v3fatal("Out of memory increasing buckets");
        }
        m_datap = newp;
        for (vluint64_t i = oldsize; i < m_dataSize; i += 64) {
            m_datap[i / 64] = 0;
        }
    }

public:
    // CONSTRUCTORS
    VlcBuckets() {
        m_dataSize = 0;
        m_datap = NULL;
        m_bucketsCovered = 0;
        allocate(1024);
    }
    ~VlcBuckets() {
        m_dataSize = 0;
        free(m_datap); m_datap = NULL;
    }

    // ACCESSORS
    static vluint64_t sufficient() { return 1; }
    vluint64_t bucketsCovered() const { return m_bucketsCovered; }

    // METHODS
    void addData(vluint64_t point, vluint64_t hits) {
        if (hits >= sufficient()) {
            // UINFO(9,"     addData "<<point<<" "<<hits<<" size="<<m_dataSize<<endl);
            if (point >= m_dataSize) allocate(point);
            m_datap[point / 64] |= covBit(point);
            m_bucketsCovered++;
        }
    }
    void clearHits(vluint64_t point) const {
        if (point >= m_dataSize) {
            return;
        } else {
            m_datap[point / 64] &= ~covBit(point);
        }
    }
    bool exists(vluint64_t point) const {
        if (point >= m_dataSize) {
            return false;
        } else {
            return (m_datap[point / 64] & covBit(point)) ? 1 : 0;
        }
    }
    vluint64_t hits(vluint64_t point) const {
        if (point >= m_dataSize) {
            return 0;
        } else {
            return (m_datap[point / 64] & covBit(point)) ? 1 : 0;
        }
    }
    vluint64_t popCount() const {
        vluint64_t pop = 0;
        for (vluint64_t i = 0; i < m_dataSize; i++) {
            if (hits(i)) pop++;
        }
        return pop;
    }
    vluint64_t dataPopCount(const VlcBuckets& remaining) {
        vluint64_t pop = 0;
        for (vluint64_t i = 0; i < m_dataSize; i++) {
            if (hits(i) && remaining.hits(i)) pop++;
        }
        return pop;
    }
    void orData(const VlcBuckets& ordata) {
        for (vluint64_t i = 0; i < m_dataSize; i++) {
            if (hits(i) && ordata.hits(i)) clearHits(i);
        }
    }

    void dump() const {
        cout << "#     ";
        for (vluint64_t i = 0; i < m_dataSize; i++) {
            if (hits(i)) cout << "," << i;
        }
        cout << endl;
    }
};

//######################################################################

#endif  // guard
