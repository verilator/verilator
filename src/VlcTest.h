// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Test/coverage file container
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_VLCTEST_H_
#define VERILATOR_VLCTEST_H_

#include "config_build.h"
#include "verilatedos.h"

#include "VlcBucket.h"
#include "VlcPoint.h"

#include <map>
#include <vector>

//********************************************************************
// VlcTest - a single testrun i.e. a file containing coverage data

class VlcTest final {
    // MEMBERS
    string m_name;  //< Name of the test
    double m_computrons;  //< Runtime for the test
    uint64_t m_testrun;  //< Test run number, for database use
    uint64_t m_rank = 0;  //< Execution rank suggestion
    uint64_t m_rankPoints = 0;  //< Ranked additional points
    uint64_t m_user = 0;  //< User data for algorithms (not persisted in .dat file)
    VlcBuckets m_buckets;  //< Coverage data for each coverage point

public:
    // CONSTRUCTORS
    VlcTest(const string& name, uint64_t testrun, double comp)
        : m_name{name}
        , m_computrons{comp}
        , m_testrun{testrun} {}
    ~VlcTest() = default;

    // ACCESSORS
    [[nodiscard]] inline const string& name() const { return m_name; }
    [[nodiscard]] inline double computrons() const { return m_computrons; }
    [[nodiscard]] inline uint64_t testrun() const { return m_testrun; }
    [[nodiscard]] inline VlcBuckets& buckets() { return m_buckets; }
    [[nodiscard]] inline uint64_t bucketsCovered() const { return m_buckets.bucketsCovered(); }
    [[nodiscard]] inline uint64_t rank() const { return m_rank; }
    inline void rank(uint64_t flag) { m_rank = flag; }
    [[nodiscard]] inline uint64_t rankPoints() const { return m_rankPoints; }
    inline void rankPoints(uint64_t flag) { m_rankPoints = flag; }
    [[nodiscard]] inline uint64_t user() const { return m_user; }
    void user(uint64_t flag) { m_user = flag; }

    // METHODS
    static void dumpHeader() {
        std::cout << "Tests:\n";
        // std::cout<<"  Testrun, Computrons,";  // Currently not loaded
        std::cout << "  Covered,     Rank,  RankPts,  Filename\n";
    }
    void dump(bool bucketsToo) const {
        if (testrun() || computrons() != 0.0) {  // currently unused // LCOV_EXCL_LINE
            std::cout << "  " << std::setw(8) << std::setfill('0') << testrun()  // LCOV_EXCL_LINE
                      << ",  " << std::setw(7) << std::setfill(' ')
                      << computrons()  // LCOV_EXCL_LINE
                      << ",";  // LCOV_EXCL_LINE
        }
        std::cout << "  " << std::setw(7) << std::setfill(' ') << bucketsCovered();
        std::cout << ",  " << std::setw(7) << std::setfill(' ') << rank();
        std::cout << ",  " << std::setw(7) << std::setfill(' ') << rankPoints();
        std::cout << ",  \"" << name() << "\"\n";
        if (bucketsToo) m_buckets.dump();
    }
};

//********************************************************************
// VlcTests - Container of all tests

class VlcTests final {
public:
    // TYPES
    using ByName = std::vector<VlcTest>;

private:
    // MEMBERS
    ByName m_tests;  //< List of all tests

    static int debug() { return V3Error::debugDefault(); }

public:
    // ITERATORS
    using iterator = ByName::iterator;
    using testIndex = size_t;
    ByName::iterator begin() { return m_tests.begin(); }
    ByName::iterator end() { return m_tests.end(); }

    // CONSTRUCTORS
    VlcTests() = default;
    ~VlcTests() = default;

    // METHODS
    void dump(bool bucketsToo) const {
        UINFO(2, "dumpTests...\n");
        VlcTest::dumpHeader();
        for (const auto& test : m_tests) test.dump(bucketsToo);
    }
    testIndex newTest(const string& name, uint64_t testrun, double comp) {
        VlcTest const test = VlcTest{name, testrun, comp};
        m_tests.emplace_back(test);
        return m_tests.size() - 1;
    }
    void clearUser() {
        for (auto& test : m_tests) test.user(0);
    }
};

//######################################################################

#endif  // Guard
