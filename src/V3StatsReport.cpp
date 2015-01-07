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

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>
#include <iomanip>

#include "V3Global.h"
#include "V3Stats.h"
#include "V3Ast.h"
#include "V3File.h"

//######################################################################
// Stats dumping

class StatsReport {
    // TYPES
    typedef vector<V3Statistic> StatColl;

    // STATE
    ofstream&	os;		// Output stream
    static StatColl	s_allStats;	///< All statistics

    void header() {
	os<<"Verilator Statistics Report\n";
	os<<endl;

	os<<"Information:"<<endl;
	os<<"  "<<v3Global.opt.version()<<endl;
	os<<"  Arguments: "<<v3Global.opt.allArgsString()<<endl;
	os<<endl;
    }

    void sumit() {
	// If sumit is set on a statistic, combine with others of same name
	typedef multimap<string,V3Statistic*> ByName;
	ByName byName;
	// * is always first
	for (StatColl::iterator it = s_allStats.begin(); it!=s_allStats.end(); ++it) {
	    V3Statistic* repp = &(*it);
	    byName.insert(make_pair(repp->name(), repp));
	}

	// Process duplicates
	V3Statistic* lastp = NULL;
	for (ByName::iterator it = byName.begin(); it!=byName.end(); ++it) {
	    V3Statistic* repp = it->second;
	    if (lastp && lastp->sumit() && lastp->printit()
		&& lastp->name() == repp->name() && lastp->stage() == repp->stage()) {
		repp->combineWith(lastp);
	    }
	    lastp = repp;
	}
    }

    void stars() {
	os<<"Global Statistics:\n";
	os<<endl;

	// Find all stages
	size_t maxWidth = 0;
	typedef multimap<string,const V3Statistic*> ByName;
	ByName byName;
	// * is always first
	for (StatColl::iterator it = s_allStats.begin(); it!=s_allStats.end(); ++it) {
	    const V3Statistic* repp = &(*it);
	    if (repp->stage() == "*" && repp->printit()) {
		if (maxWidth < repp->name().length()) maxWidth = repp->name().length();
		byName.insert(make_pair(repp->name(), repp));
	    }
	}

	// Print organized by stage
	for (ByName::iterator it = byName.begin(); it!=byName.end(); ++it) {
	    const V3Statistic* repp = it->second;
	    os<<"  "<<left<<setw(maxWidth)<<repp->name();
	    repp->dump(os);
	    os<<endl;
	}
	os<<endl;
    }

    void stages() {
	os<<"Stage Statistics:\n";

	// Find all stages
	int stage=0;
	size_t maxWidth = 0;
	typedef vector<string> Stages;
	Stages stages;
	map<string,int> stageInt;
	typedef multimap<string,const V3Statistic*> ByName;
	ByName byName;
	// * is always first
	for (StatColl::iterator it = s_allStats.begin(); it!=s_allStats.end(); ++it) {
	    const V3Statistic* repp = &(*it);
	    if (repp->stage() != "*" && repp->printit()) {
		if (maxWidth < repp->name().length()) maxWidth = repp->name().length();
		if (stageInt.find(repp->stage()) == stageInt.end()) {
		    stageInt.insert(make_pair(repp->stage(), stage++));
		    stages.push_back(repp->stage());
		}
		byName.insert(make_pair(repp->name(), repp));
	    }
	}

	// Header
	os<<"  Stat     "<<left<<setw(maxWidth-5-2)<<"";
	for (Stages::iterator it = stages.begin(); it!=stages.end(); ++it) {
	    os<<"  "<<left<<setw(9)<<*it;
	}
	os<<endl;
	os<<"  -------- "<<left<<setw(maxWidth-5-2)<<"";
	for (Stages::iterator it = stages.begin(); it!=stages.end(); ++it) {
	    os<<"  "<<left<<setw(9)<<"-------";
	}
	//os<<endl;

	// Print organized by stage
	string lastName = "__NONE__";
	string lastCommaName = "__NONE__";
	unsigned col=0;
	for (ByName::iterator it = byName.begin(); it!=byName.end(); ++it) {
	    const V3Statistic* repp = it->second;
	    if (lastName != repp->name()) {
		lastName = repp->name();
		{
		    string commaName = lastName;
		    string::size_type pos;
		    if ((pos=commaName.find(",")) != string::npos) {
			commaName.erase(pos);
		    }
		    if (lastCommaName != commaName) {
			lastCommaName = commaName;
			os<<endl;
		    }
		}
		os<<endl;
		col = 0;
		os<<"  "<<left<<setw(maxWidth)<<repp->name();
	    }
	    while (col<stages.size() && stages.at(col) != repp->stage()) {
		os<<setw(11)<<"";
		col++;
	    }
	    repp->dump(os);
	    col++;
	}
	os<<endl;
    }

public:
    // METHODS
    static void addStat(const V3Statistic& stat) {
	s_allStats.push_back(stat);
    }

    // CONSTRUCTORS
    StatsReport(ofstream* aofp)
	: os(*aofp) {
	header();
	sumit();
	stars();
	stages();
    }
    ~StatsReport() {}
};

StatsReport::StatColl	StatsReport::s_allStats;

//######################################################################
// V3Statstic class

void V3Statistic::dump (ofstream& os) const {
    os<<"  "<<right<<fixed<<setprecision(0)<<setw(9)<<count();
}

//######################################################################
// Top Stats class

void V3Stats::addStat(const V3Statistic& stat) {
    StatsReport::addStat(stat);
}

void V3Stats::statsReport() {
    UINFO(2,__FUNCTION__<<": "<<endl);

    // Open stats file
    string filename = v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"__stats.txt";
    ofstream* ofp (V3File::new_ofstream(filename));
    if (ofp->fail()) v3fatalSrc("Can't write "<<filename);

    StatsReport reporter (ofp);

    // Cleanup
    ofp->close(); delete ofp; ofp = NULL;
}
