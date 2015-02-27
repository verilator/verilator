// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: top implementation
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
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

#include "V3Error.h"
#include "V3Os.h"
#include "VlcOptions.h"
#include "VlcTop.h"

#include <sys/stat.h>
#include <fstream>
#include <algorithm>

//######################################################################

void VlcTop::readCoverage(const string& filename, bool nonfatal) {
    UINFO(2,"readCoverage "<<filename<<endl);

    ifstream is (filename.c_str());
    if (!is) {
	if (!nonfatal) v3fatal("Can't read "<<filename);
	return;
    }

    // Testrun and computrons argument unsupported as yet
    VlcTest* testp = tests().newTest(filename, 0, 0);

    while (!is.eof()) {
	string line;
	getline(is, line);
	//UINFO(9," got "<<line<<endl);
	if (line[0] == 'C') {
	    string::size_type secspace=3;
	    for (; secspace<line.length(); secspace++) {
		if (line[secspace]=='\'' && line[secspace+1]==' ') break;
	    }
	    string point = line.substr(3,secspace-3);
	    vluint64_t hits = atoll(line.c_str()+secspace+1);
	    //UINFO(9,"   point '"<<point<<"'"<<" "<<hits<<endl);

	    vluint64_t pointnum = points().findAddPoint(point, hits);
	    if (pointnum) {} // Prevent unused
	    if (opt.rank()) {  // Only if ranking - uses a lot of memory
		if (hits >= VlcBuckets::sufficient()) {
		    points().pointNumber(pointnum).testsCoveringInc();
		    testp->buckets().addData(pointnum, hits);
		}
	    }
	}
    }
}

void VlcTop::writeCoverage(const string& filename) {
    UINFO(2,"writeCoverage "<<filename<<endl);

    ofstream os (filename.c_str());
    if (!os) {
	v3fatal("Can't write "<<filename);
	return;
    }

    os << "# SystemC::Coverage-3" << endl;
    for (VlcPoints::ByName::iterator it=m_points.begin(); it!=m_points.end(); ++it) {
	const VlcPoint& point = m_points.pointNumber(it->second);
	os <<"C '"<<point.name()<<"' " << point.count()<<endl;
    }
}

//********************************************************************

struct CmpComputrons {
    inline bool operator () (const VlcTest* lhsp, const VlcTest* rhsp) const {
	if (lhsp->computrons() != rhsp->computrons()) {
	    return lhsp->computrons() < rhsp->computrons();
	}
	return lhsp->bucketsCovered() > rhsp->bucketsCovered();
    }
};

void VlcTop::rank() {
    UINFO(2,"rank...\n");
    vluint64_t nextrank=1;

    // Sort by computrons, so fast tests get selected first
    vector<VlcTest*> bytime;
    for (VlcTests::ByName::iterator it=m_tests.begin(); it!=m_tests.end(); ++it) {
	VlcTest* testp = *it;
	if (testp->bucketsCovered()) {	 // else no points, so can't help us
	    bytime.push_back(*it);
	}
    }
    sort(bytime.begin(), bytime.end(), CmpComputrons()); // Sort the vector

    VlcBuckets remaining;
    for (VlcPoints::ByName::iterator it=m_points.begin(); it!=m_points.end(); ++it) {
	VlcPoint* pointp = &points().pointNumber(it->second);
	// If any tests hit this point, then we'll need to cover it.
	if (pointp->testsCovering()) { remaining.addData(pointp->pointNum(), 1); }
    }

    // Additional Greedy algorithm
    // O(n^2) Ouch.  Probably the thing to do is randomize the order of data
    // then hierarchically solve a small subset of tests, and take resulting
    // solution and move up to larger subset of tests.  (Aka quick sort.)
    while (1) {
	if (debug()) { UINFO(9,"Left on iter"<<nextrank<<": "); remaining.dump(); }
	VlcTest* bestTestp = NULL;
	vluint64_t bestRemain = 0;
	for (vector<VlcTest*>::iterator it=bytime.begin(); it!=bytime.end(); ++it) {
	    VlcTest* testp = *it;
	    if (!testp->rank()) {
		vluint64_t remain = testp->buckets().dataPopCount(remaining);
		if (remain > bestRemain) {
		    bestTestp = testp;
		    bestRemain = remain;
		}
	    }
	}
	if (VlcTest* testp = bestTestp) {
	    testp->rank(nextrank++);
	    testp->rankPoints(bestRemain);
	    remaining.orData(bestTestp->buckets());
	} else {
	    break;   // No test covering more stuff found
	}
    }
}

//######################################################################

void VlcTop::annotateCalc() {
    // Calculate per-line information into filedata structure
    for (VlcPoints::ByName::iterator it=m_points.begin(); it!=m_points.end(); ++it) {
	const VlcPoint& point = m_points.pointNumber(it->second);
	string filename = point.filename();
	int lineno = point.lineno();
	if (filename!="" && lineno!=0) {
	    int column = point.column();
	    VlcSource& source = sources().findNewSource(filename);
	    string threshStr = point.thresh();
	    unsigned thresh = (threshStr!="") ? atoi(threshStr.c_str()) : opt.annotateMin();
	    bool ok = (point.count() >= thresh);
	    UINFO(9, "AnnoCalc count "<<filename<<" "<<lineno<<" "<<point.count()<<endl);
	    source.incCount(lineno, column, point.count(), ok);
	}
    }
}

void VlcTop::annotateCalcNeeded() {
    // Compute which files are needed.  A file isn't needed if it has appropriate
    // coverage in all categories
    int totCases = 0;
    int totOk = 0;
    for (VlcSources::NameMap::iterator sit=m_sources.begin(); sit!=m_sources.end(); ++sit) {
	VlcSource& source = sit->second;
	//UINFO(1,"Source "<<source.name()<<endl);
	if (opt.annotateAll()) source.needed(true);
	VlcSource::LinenoMap& lines = source.lines();
	for (VlcSource::LinenoMap::iterator lit=lines.begin(); lit!=lines.end(); ++lit) {
	    VlcSource::ColumnMap& cmap = lit->second;
	    for (VlcSource::ColumnMap::iterator cit=cmap.begin(); cit!=cmap.end(); ++cit) {
		VlcSourceCount& col = cit->second;
		//UINFO(0,"Source "<<source.name()<<" lineno="<<col.lineno()<<" col="<<col.column()<<endl);
		++totCases;
		if (col.ok()) {
		    ++totOk;
		} else {
		    source.needed(true);
		}
	    }
	}
    }
    float pct = totCases ? (100*totOk / totCases) : 0;
    cout<<"Total coverage ("<<totOk<<"/"<<totCases<<") "
	<<fixed<<setw(3)<<setprecision(2)<<pct<<"%"<<endl;
    if (totOk != totCases) cout<<"See lines with '%00' in "<<opt.annotateOut()<<endl;
}

void VlcTop::annotateOutputFiles(const string& dirname) {
    // Create if uncreated, ignore errors
    V3Os::createDir(dirname);
    for (VlcSources::NameMap::iterator sit=m_sources.begin(); sit!=m_sources.end(); ++sit) {
	VlcSource& source = sit->second;
	if (!source.needed()) continue;
	string filename = source.name();
	string outfilename = dirname+"/"+V3Os::filenameNonDir(filename);

	UINFO(1,"annotateOutputFile "<<filename<<" -> "<<outfilename<<endl);

	ifstream is (filename.c_str());
	if (!is) {
	    v3error("Can't read "<<filename);
	    return;
	}
	
	ofstream os (outfilename.c_str());
	if (!os) {
	    v3fatal("Can't write "<<outfilename);
	    return;
	}

	os << "\t// verilator_coverage annotation"<<endl;

	int lineno = 0;
	while (!is.eof()) {
	    lineno++;
	    string line;
	    getline(is, line);

	    bool first = true;

	    VlcSource::LinenoMap& lines = source.lines();
	    VlcSource::LinenoMap::iterator lit=lines.find(lineno);
	    if (lit != lines.end()) {
		VlcSource::ColumnMap& cmap = lit->second;
		for (VlcSource::ColumnMap::iterator cit=cmap.begin(); cit!=cmap.end(); ++cit) {
		    VlcSourceCount& col = cit->second;
		    //UINFO(0,"Source "<<source.name()<<" lineno="<<col.lineno()<<" col="<<col.column()<<endl);
		    os<<(col.ok()?" ":"%")
		      <<setfill('0')<<setw(6)<<col.count()
		      <<"\t"<<line<<endl;
		    if (first) {
			first = false;
			// Multiple columns on same line; print line just once
			string indent = "";
			for (const char* cp=line.c_str(); isspace(*cp); ++cp) {
			    indent += *cp;
			}
			line = indent + "verilator_coverage: (next point on previous line)\n";
		    }
		}
	    }

	    if (first) {
		os<<"\t"<<line<<endl;
	    }
	}
    }
}

void VlcTop::annotate(const string& dirname) {
    // Calculate per-line information into filedata structure
    annotateCalc();
    annotateCalcNeeded();
    annotateOutputFiles(dirname);
}

