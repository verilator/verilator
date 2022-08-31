// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: top implementation
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

#include "VlcTop.h"

#include "V3Error.h"
#include "V3Os.h"

#include "VlcOptions.h"

#include <algorithm>
#include <fstream>
#include <string>
#include <vector>

//######################################################################

void VlcTop::readCoverage(const string& filename, bool nonfatal) {
    UINFO(2, "readCoverage " << filename << endl);

    std::ifstream is{filename.c_str()};
    if (!is) {
        if (!nonfatal) v3fatal("Can't read " << filename);
        return;
    }

    // Testrun and computrons argument unsupported as yet
    VlcTest* const testp = tests().newTest(filename, 0, 0);

    while (!is.eof()) {
        const string line = V3Os::getline(is);
        // UINFO(9," got "<<line<<endl);
        if (line[0] == 'C') {
            string::size_type secspace = 3;
            for (; secspace < line.length(); secspace++) {
                if (line[secspace] == '\'' && line[secspace + 1] == ' ') break;
            }
            const string point = line.substr(3, secspace - 3);
            uint64_t hits = std::atoll(line.c_str() + secspace + 1);
            // UINFO(9,"   point '"<<point<<"'"<<" "<<hits<<endl);

            uint64_t pointnum = points().findAddPoint(point, hits);
            if (pointnum) {}  // Prevent unused
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
    UINFO(2, "writeCoverage " << filename << endl);

    std::ofstream os{filename.c_str()};
    if (!os) {
        v3fatal("Can't write " << filename);
        return;
    }

    os << "# SystemC::Coverage-3\n";
    for (const auto& i : m_points) {
        const VlcPoint& point = m_points.pointNumber(i.second);
        os << "C '" << point.name() << "' " << point.count() << '\n';
    }
}

void VlcTop::writeInfo(const string& filename) {
    UINFO(2, "writeInfo " << filename << endl);

    std::ofstream os{filename.c_str()};
    if (!os) {
        v3fatal("Can't write " << filename);
        return;
    }

    annotateCalc();

    // See 'man lcov' for format details
    // TN:<trace_file_name>
    // Source file:
    //   SF:<absolute_path_to_source_file>
    //   FN:<line_number_of_function_start>,<function_name>
    //   FNDA:<execution_count>,<function_name>
    //   FNF:<number_functions_found>
    //   FNH:<number_functions_hit>
    // Branches:
    //   BRDA:<line_number>,<block_number>,<branch_number>,<taken_count_or_-_for_zero>
    //   BRF:<number_of_branches_found>
    //   BRH:<number_of_branches_hit>
    // Line counts:
    //   DA:<line_number>,<execution_count>
    //   LF:<number_of_lines_found>
    //   LH:<number_of_lines_hit>
    // Section ending:
    //   end_of_record

    os << "TN:verilator_coverage\n";
    for (auto& si : m_sources) {
        VlcSource& source = si.second;
        os << "SF:" << source.name() << '\n';
        VlcSource::LinenoMap& lines = source.lines();
        for (auto& li : lines) {
            const int lineno = li.first;
            VlcSource::ColumnMap& cmap = li.second;
            bool first = true;
            uint64_t min_count = 0;  // Minimum across all columns on line
            for (auto& ci : cmap) {
                VlcSourceCount& col = ci.second;
                if (first) {
                    min_count = col.count();
                    first = false;
                } else {
                    min_count = std::min(min_count, col.count());
                }
            }
            os << "DA:" << lineno << "," << min_count << "\n";
        }
        os << "end_of_record\n";
    }
}

//********************************************************************

struct CmpComputrons {
    bool operator()(const VlcTest* lhsp, const VlcTest* rhsp) const {
        if (lhsp->computrons() != rhsp->computrons()) {
            return lhsp->computrons() < rhsp->computrons();
        }
        return lhsp->bucketsCovered() > rhsp->bucketsCovered();
    }
};

void VlcTop::rank() {
    UINFO(2, "rank...\n");
    uint64_t nextrank = 1;

    // Sort by computrons, so fast tests get selected first
    std::vector<VlcTest*> bytime;
    for (const auto& testp : m_tests) {
        if (testp->bucketsCovered()) {  // else no points, so can't help us
            bytime.push_back(testp);
        }
    }
    sort(bytime.begin(), bytime.end(), CmpComputrons());  // Sort the vector

    VlcBuckets remaining;
    for (const auto& i : m_points) {
        const VlcPoint* const pointp = &points().pointNumber(i.second);
        // If any tests hit this point, then we'll need to cover it.
        if (pointp->testsCovering()) remaining.addData(pointp->pointNum(), 1);
    }

    // Additional Greedy algorithm
    // O(n^2) Ouch.  Probably the thing to do is randomize the order of data
    // then hierarchically solve a small subset of tests, and take resulting
    // solution and move up to larger subset of tests.  (Aka quick sort.)
    while (true) {
        if (debug()) {
            UINFO(9, "Left on iter" << nextrank << ": ");  // LCOV_EXCL_LINE
            remaining.dump();  // LCOV_EXCL_LINE
        }
        VlcTest* bestTestp = nullptr;
        uint64_t bestRemain = 0;
        for (const auto& testp : bytime) {
            if (!testp->rank()) {
                uint64_t remain = testp->buckets().dataPopCount(remaining);
                if (remain > bestRemain) {
                    bestTestp = testp;
                    bestRemain = remain;
                }
            }
        }
        if (VlcTest* const testp = bestTestp) {
            testp->rank(nextrank++);
            testp->rankPoints(bestRemain);
            remaining.orData(bestTestp->buckets());
        } else {
            break;  // No test covering more stuff found
        }
    }
}

//######################################################################

void VlcTop::annotateCalc() {
    // Calculate per-line information into filedata structure
    for (const auto& i : m_points) {
        const VlcPoint& point = m_points.pointNumber(i.second);
        const string filename = point.filename();
        const int lineno = point.lineno();
        if (!filename.empty() && lineno != 0) {
            VlcSource& source = sources().findNewSource(filename);
            const string threshStr = point.thresh();
            unsigned thresh
                = (!threshStr.empty()) ? std::atoi(threshStr.c_str()) : opt.annotateMin();
            const bool ok = (point.count() >= thresh);
            UINFO(9, "AnnoCalc count " << filename << ":" << lineno << ":" << point.column() << " "
                                       << point.count() << " " << point.linescov() << '\n');
            // Base coverage
            source.incCount(lineno, point.column(), point.count(), ok);
            // Additional lines covered by this statement
            bool range = false;
            int start = 0;
            int end = 0;
            const string linescov = point.linescov();
            for (const char* covp = linescov.c_str(); true; ++covp) {
                if (!*covp || *covp == ',') {  // Ending
                    for (int lni = start; start && lni <= end; ++lni) {
                        source.incCount(lni, point.column(), point.count(), ok);
                    }
                    if (!*covp) break;
                    start = 0;  // Prep for next
                    end = 0;
                    range = false;
                } else if (*covp == '-') {
                    range = true;
                } else if (std::isdigit(*covp)) {
                    const char* const digitsp = covp;
                    while (std::isdigit(*covp)) ++covp;
                    --covp;  // Will inc in for loop
                    if (!range) start = std::atoi(digitsp);
                    end = std::atoi(digitsp);
                }
            }
        }
    }
}

void VlcTop::annotateCalcNeeded() {
    // Compute which files are needed.  A file isn't needed if it has appropriate
    // coverage in all categories
    int totCases = 0;
    int totOk = 0;
    for (auto& si : m_sources) {
        VlcSource& source = si.second;
        // UINFO(1,"Source "<<source.name()<<endl);
        if (opt.annotateAll()) source.needed(true);
        VlcSource::LinenoMap& lines = source.lines();
        for (auto& li : lines) {
            VlcSource::ColumnMap& cmap = li.second;
            for (auto& ci : cmap) {
                VlcSourceCount& col = ci.second;
                // UINFO(0,"Source "<<source.name()<<":"<<col.lineno()<<":"<<col.column()<<endl);
                ++totCases;
                if (col.ok()) {
                    ++totOk;
                } else {
                    source.needed(true);
                }
            }
        }
    }
    const float pct = totCases ? (100 * totOk / totCases) : 0;
    cout << "Total coverage (" << totOk << "/" << totCases << ") ";
    cout << std::fixed << std::setw(3) << std::setprecision(2) << pct << "%\n";
    if (totOk != totCases) cout << "See lines with '%00' in " << opt.annotateOut() << '\n';
}

void VlcTop::annotateOutputFiles(const string& dirname) {
    // Create if uncreated, ignore errors
    V3Os::createDir(dirname);
    for (auto& si : m_sources) {
        VlcSource& source = si.second;
        if (!source.needed()) continue;
        const string filename = source.name();
        const string outfilename = dirname + "/" + V3Os::filenameNonDir(filename);

        UINFO(1, "annotateOutputFile " << filename << " -> " << outfilename << endl);

        std::ifstream is{filename.c_str()};
        if (!is) {
            v3error("Can't read " << filename);
            return;
        }

        std::ofstream os{outfilename.c_str()};
        if (!os) {
            v3fatal("Can't write " << outfilename);
            return;
        }

        os << "\t// verilator_coverage annotation\n";

        int lineno = 0;
        while (!is.eof()) {
            lineno++;
            string line = V3Os::getline(is);

            bool first = true;

            VlcSource::LinenoMap& lines = source.lines();
            const auto lit = lines.find(lineno);
            if (lit != lines.end()) {
                VlcSource::ColumnMap& cmap = lit->second;
                for (auto& ci : cmap) {
                    VlcSourceCount& col = ci.second;
                    // UINFO(0,"Source
                    // "<<source.name()<<":"<<col.lineno()<<":"<<col.column()<<endl);
                    os << (col.ok() ? " " : "%") << std::setfill('0') << std::setw(6)
                       << col.count() << "\t" << line << '\n';
                    if (first) {
                        first = false;
                        // Multiple columns on same line; print line just once
                        string indent;
                        for (string::const_iterator pos = line.begin();
                             pos != line.end() && std::isspace(*pos); ++pos) {
                            indent += *pos;
                        }
                        line = indent + "verilator_coverage: (next point on previous line)\n";
                    }
                }
            }

            if (first) os << "\t" << line << '\n';
        }
    }
}

void VlcTop::annotate(const string& dirname) {
    // Calculate per-line information into filedata structure
    annotateCalc();
    annotateCalcNeeded();
    annotateOutputFiles(dirname);
}
