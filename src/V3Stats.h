// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2005-2015 by Wilson Snyder.  This program is free software; you can
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

#ifndef _V3STATS_H_
#define _V3STATS_H_ 1
#include "config_build.h"
#include "verilatedos.h"
#include "V3Error.h"

class AstNetlist;

//============================================================================

class V3Double0 {
    // Double counter, initializes to zero for easy use
    double	m_d;	///< Count of occurrences/ value
public:
    // METHODS
    V3Double0() : m_d(0) {}
    ~V3Double0() {}

    // Implicit conversion operators:
    inline V3Double0 (const vluint64_t v) : m_d(v) { }
    inline operator double () const { return m_d; }

    // Explicit operators:
    inline V3Double0& operator++() { ++m_d; return *this; }	// prefix
    inline V3Double0  operator++(int) { V3Double0 old=*this; m_d++; return old; }	// postfix
    inline V3Double0& operator= (const double v) { m_d = v; return *this; }
    inline V3Double0& operator+=(const double v) { m_d += v; return *this; }
    inline V3Double0& operator-=(const double v) { m_d -= v; return *this; }
};

//============================================================================

class V3Statistic {
    // A statistical entry we want published into the database
    string	m_name;		///< Nameiption of this statistic
    double	m_count;	///< Count of occurrences/ value
    string	m_stage;	///< Runtime stage
    bool	m_sumit;	///< Do summation of similar stats
    bool	m_printit;	///< Print the results
public:
    // METHODS
    string stage() const { return m_stage; }
    string name() const { return m_name; }
    double count() const { return m_count; }
    bool sumit() const { return m_sumit; }
    bool printit() const { return m_printit; }
    virtual void dump(ofstream& os) const;
    void combineWith(V3Statistic* otherp) {
	m_count += otherp->count();
	otherp->m_printit = false;
    }
    // CONSTRUCTORS
    V3Statistic(const string& stage, const string& name, double count, bool sumit=false)
	: m_name(name), m_count(count), m_stage(stage), m_sumit(sumit)
	, m_printit(true) {}
    virtual ~V3Statistic() {}
};

//============================================================================

class V3Stats {
public:
    static void addStat(const V3Statistic&);
    static void addStat(const string& stage, const string& name, double count) {
	addStat(V3Statistic(stage,name,count)); }
    static void addStat(const string& name, double count) {
	addStat(V3Statistic("*",name,count)); }
    static void addStatSum(const string& name, double count) {
	addStat(V3Statistic("*",name,count,true)); }
    /// Called by the top level to collect statistics
    static void statsStageAll(AstNetlist* nodep, const string& stage, bool fast=false);
    static void statsFinalAll(AstNetlist* nodep);
    /// Called by the top level to dump the statistics
    static void statsReport();
};


#endif // Guard
