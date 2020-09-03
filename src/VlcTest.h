// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Test/coverage file container
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

#ifndef _VLCTEST_H_
#define _VLCTEST_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "VlcPoint.h"
#include "VlcBucket.h"

#include <map>
#include <vector>

//********************************************************************
// VlcTest - a single testrun i.e. a file containing coverage data

class VlcTest {
private:
    // MEMBERS
    string m_name;  //< Name of the test
    double m_computrons;  //< Runtime for the test
    vluint64_t m_testrun;  //< Test run number, for database use
    vluint64_t m_rank = 0;  //< Execution rank suggestion
    vluint64_t m_rankPoints = 0;  //< Ranked additional points
    vluint64_t m_user = 0;  //< User data for algorithms (not persisted in .dat file)
    VlcBuckets m_buckets;  //< Coverage data for each coverage point

public:
    // CONSTRUCTORS
    VlcTest(const string& name, vluint64_t testrun, double comp)
        : m_name{name}
        , m_computrons{comp}
        , m_testrun{testrun} {}
    ~VlcTest() {}

    // ACCESSORS
    const string& name() const { return m_name; }
    double computrons() const { return m_computrons; }
    vluint64_t testrun() const { return m_testrun; }
    VlcBuckets& buckets() { return m_buckets; }
    vluint64_t bucketsCovered() const { return m_buckets.bucketsCovered(); }
    vluint64_t rank() const { return m_rank; }
    void rank(vluint64_t flag) { m_rank = flag; }
    vluint64_t rankPoints() const { return m_rankPoints; }
    void rankPoints(vluint64_t flag) { m_rankPoints = flag; }
    vluint64_t user() const { return m_user; }
    void user(vluint64_t flag) { m_user = flag; }

    // METHODS
    static void dumpHeader() {
        cout << "Tests:\n";
        // cout<<"  Testrun, Computrons,";  // Currently not loaded
        cout << "  Covered,     Rank,  RankPts,  Filename" << endl;
    }
    void dump(bool bucketsToo) {
        if (testrun() || computrons() != 0.0) {  // currently unused // LCOV_EXCL_LINE
            cout << "  " << std::setw(8) << std::setfill('0') << testrun()  // LCOV_EXCL_LINE
                 << ",  " << std::setw(7) << std::setfill(' ') << computrons()  // LCOV_EXCL_LINE
                 << ",";  // LCOV_EXCL_LINE
        }
        cout << "  " << std::setw(7) << std::setfill(' ') << bucketsCovered();
        cout << ",  " << std::setw(7) << std::setfill(' ') << rank();
        cout << ",  " << std::setw(7) << std::setfill(' ') << rankPoints();
        cout << ",  \"" << name() << "\"" << endl;
        if (bucketsToo) m_buckets.dump();
    }
};

//********************************************************************
// VlcTests - Container of all tests

class VlcTests {
public:
    // TYPES
    typedef std::vector<VlcTest*> ByName;

private:
    // MEMBERS
    ByName m_tests;  //< List of all tests

public:
    // ITERATORS
    typedef ByName::iterator iterator;
    ByName::iterator begin() { return m_tests.begin(); }
    ByName::iterator end() { return m_tests.end(); }

    // CONSTRUCTORS
    VlcTests() {}
    ~VlcTests() {
        for (auto it = begin(); it != end(); ++it) { VL_DO_CLEAR(delete *it, *it = nullptr); }
    }

    // METHODS
    void dump(bool bucketsToo) {
        UINFO(2, "dumpTests...\n");
        VlcTest::dumpHeader();
        for (const auto& testp : m_tests) testp->dump(bucketsToo);
    }
    VlcTest* newTest(const string& name, vluint64_t testrun, double comp) {
        VlcTest* testp = new VlcTest(name, testrun, comp);
        m_tests.push_back(testp);
        return testp;
    }
    void clearUser() {
        for (const auto& testp : m_tests) testp->user(0);
    }
};

//######################################################################

#endif  // Guard
