// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3STATS_H_
#define VERILATOR_V3STATS_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"

class AstNetlist;

//============================================================================

class VDouble0 final {
    // Double counter, initializes to zero for easy use
    double m_d = 0.0;  ///< Count of occurrences/ value
public:
    // METHODS
    VDouble0() = default;
    ~VDouble0() = default;

    // Implicit conversion operators:
    explicit VDouble0(const uint64_t v)
        : m_d{static_cast<double>(v)} {}
    operator double() const { return m_d; }

    // Explicit operators:
    VDouble0& operator++() {  // prefix
        ++m_d;
        return *this;
    }
    VDouble0 operator++(int) {  // postfix
        VDouble0 old = *this;
        m_d++;
        return old;
    }
    VDouble0& operator=(const double v) {
        m_d = v;
        return *this;
    }
    VDouble0& operator+=(const double v) {
        m_d += v;
        return *this;
    }
    VDouble0& operator-=(const double v) {
        m_d -= v;
        return *this;
    }
};

//============================================================================

class V3Statistic final {
    // A statistical entry we want published into the database
    const string m_name;  ///< Name of this statistic
    double m_value;  ///< Value of statistic (count, ratio, etc.)
    unsigned m_precision;  ///< Precision to print with (number of fractional digits)
    const string m_stage;  ///< Runtime stage
    const bool m_sumit;  ///< Do summation of similar stats
    const bool m_perf;  ///< Performance section
    bool m_printit = true;  ///< Print the results
public:
    // METHODS
    string stage() const VL_MT_SAFE { return m_stage; }
    string name() const VL_MT_SAFE { return m_name; }
    double value() const VL_MT_SAFE { return m_value; }
    unsigned precision() const VL_MT_SAFE { return m_precision; }
    bool sumit() const VL_MT_SAFE { return m_sumit; }
    bool perf() const VL_MT_SAFE { return m_perf; }
    bool printit() const VL_MT_SAFE { return m_printit; }
    virtual void dump(std::ofstream& os) const VL_MT_SAFE;
    void combineWith(V3Statistic* otherp) {
        m_value += otherp->value();
        otherp->m_printit = false;
    }
    // CONSTRUCTORS
    V3Statistic(const string& stage, const string& name, double value, unsigned precision,
                bool sumit = false, bool perf = false)
        : m_name{name}
        , m_value{value}
        , m_precision{precision}
        , m_stage{stage}
        , m_sumit{sumit}
        , m_perf{perf} {}
    virtual ~V3Statistic() = default;
};

//============================================================================

class V3Stats final {
public:
    static void addStat(const V3Statistic&);
    static void addStat(const string& stage, const string& name, double value,
                        unsigned precision = 0) {
        addStat(V3Statistic{stage, name, value, precision});
    }
    static void addStat(const string& name, double value, unsigned precision = 0) {
        addStat(V3Statistic{"*", name, value, precision});
    }
    static void addStatSum(const string& name, double count) {
        addStat(V3Statistic{"*", name, count, 0, true});
    }
    static void addStatPerf(const string& name, double value) {
        addStat(V3Statistic{"*", name, value, 6, true, true});
    }
    /// Called each stage
    static void statsStage(const string& name);
    /// Called by the top level to collect statistics
    static void statsStageAll(AstNetlist* nodep, const string& stage, bool fastOnly = false);
    static void statsFinalAll(AstNetlist* nodep);
    /// Called by the top level to dump the statistics
    static void statsReport();
    /// Called by debug dumps
    static void infoHeader(std::ofstream& os, const string& prefix);
};

#endif  // Guard
