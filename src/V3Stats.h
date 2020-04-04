// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3STATS_H_
#define _V3STATS_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"

class AstNetlist;

//============================================================================

class VDouble0 {
    // Double counter, initializes to zero for easy use
    double m_d;  ///< Count of occurrences/ value
public:
    // METHODS
    VDouble0() : m_d(0) {}
    ~VDouble0() {}

    // Implicit conversion operators:
    inline explicit VDouble0(const vluint64_t v) : m_d(v) { }
    inline operator double() const { return m_d; }

    // Explicit operators:
    inline VDouble0& operator++() { ++m_d; return *this; }  // prefix
    inline VDouble0  operator++(int) { VDouble0 old=*this; m_d++; return old; }  // postfix
    inline VDouble0& operator= (const double v) { m_d = v; return *this; }
    inline VDouble0& operator+=(const double v) { m_d += v; return *this; }
    inline VDouble0& operator-=(const double v) { m_d -= v; return *this; }
};

//============================================================================

class V3Statistic {
    // A statistical entry we want published into the database
    string      m_name;         ///< Nameiption of this statistic
    double      m_count;        ///< Count of occurrences/ value
    string      m_stage;        ///< Runtime stage
    bool        m_sumit;        ///< Do summation of similar stats
    bool        m_perf;         ///< Performance section
    bool        m_printit;      ///< Print the results
public:
    // METHODS
    string stage() const { return m_stage; }
    string name() const { return m_name; }
    double count() const { return m_count; }
    bool sumit() const { return m_sumit; }
    bool perf() const { return m_perf; }
    bool printit() const { return m_printit; }
    virtual void dump(std::ofstream& os) const;
    void combineWith(V3Statistic* otherp) {
        m_count += otherp->count();
        otherp->m_printit = false;
    }
    // CONSTRUCTORS
    V3Statistic(const string& stage, const string& name,
                double count, bool sumit=false, bool perf=false)
        : m_name(name), m_count(count), m_stage(stage), m_sumit(sumit), m_perf(perf)
        , m_printit(true) {}
    virtual ~V3Statistic() {}
};

//============================================================================

class V3Stats {
public:
    static void addStat(const V3Statistic&);
    static void addStat(const string& stage, const string& name, double count) {
        addStat(V3Statistic(stage, name, count)); }
    static void addStat(const string& name, double count) {
        addStat(V3Statistic("*", name, count)); }
    static void addStatSum(const string& name, double count) {
        addStat(V3Statistic("*", name, count, true)); }
    static void addStatPerf(const string& name, double count) {
        addStat(V3Statistic("*", name, count, true, true)); }
    /// Called each stage
    static void statsStage(const string& name);
    /// Called by the top level to collect statistics
    static void statsStageAll(AstNetlist* nodep, const string& stage, bool fast=false);
    static void statsFinalAll(AstNetlist* nodep);
    /// Called by the top level to dump the statistics
    static void statsReport();
};


#endif  // Guard
