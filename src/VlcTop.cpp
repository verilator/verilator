// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: top implementation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#define VL_MT_DISABLED_CODE_UNIT 1

#include "VlcTop.h"

#include "V3Error.h"
#include "V3Os.h"

#include "VlcOptions.h"

#include <algorithm>
#include <fstream>
#include <iomanip>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

//######################################################################

namespace {

// Report helpers only.  They keep the flat summary and hierarchy report using
// the same hit/total accounting and output formatting.  These helpers read the
// fields already exposed by VlcPoint; they do not affect coverage point
// identity, merging, or .dat writing.

// Map coverage type to (covered points, total points).
using TypeTally = std::map<std::string, std::pair<uint64_t, uint64_t>>;

static const char* const s_orderedTypes[]
    = {"line", "toggle", "branch", "expr", "fsm_state", "fsm_arc"};
static const size_t s_summaryIndent = 2;
static const size_t s_reportRowIndent = 4;

string displayType(const VlcPoint& point) {
    const string type = point.type();
    return type.empty() ? "point" : type;
}

bool isCollapsedHier(const string& hier) {
    return hier.find('*') != string::npos || hier.find('?') != string::npos;
}

bool isOrderedType(const string& type) {
    for (const char* const typep : s_orderedTypes) {
        if (type == typep) return true;
    }
    return false;
}

string reportHier(const VlcPoint& point) {
    // FSM records currently have useful instance scope in Fv.
    if (point.isFsmState() || point.isFsmArc()) {
        const string fsmVar = point.fsmVarName();
        return fsmVar.substr(0, fsmVar.rfind('.'));
    }
    return point.hier();
}

std::vector<string> splitHier(const string& hier) {
    // Verilator emits dot-separated non-empty hierarchy components.
    std::vector<string> parts;
    string::size_type start = 0;
    while (true) {
        const string::size_type dot = hier.find('.', start);
        if (dot == string::npos) break;
        parts.push_back(hier.substr(start, dot - start));
        start = dot + 1;
    }
    parts.push_back(hier.substr(start));
    return parts;
}

string duName(const VlcPoint& point) {
    // Pages are emitted as v_<type>/<design-unit> for RTL coverage.  Use the
    // suffix as the design-unit summary key.
    const string page = point.page();
    return page.substr(page.find('/') + 1);
}

void tallyPoint(TypeTally& tally, const string& type, uint64_t count) {
    std::pair<uint64_t, uint64_t>& entry = tally[type];
    if (count > 0) ++entry.first;
    ++entry.second;
}

// Keep the percentage calculation in one place so flat summaries and hierarchy
// reports cannot drift in formatting or zero-total handling.
double pct(uint64_t hit, uint64_t total) {
    return total ? (100.0 * static_cast<double>(hit) / static_cast<double>(total)) : 0.0;
}

// Shared row formatter.  The callers choose which rows to print; this only keeps
// the text layout identical between the flat and hierarchy reports.
void printIndent(size_t indent) {
    for (size_t i = 0; i < indent; ++i) std::cout << ' ';
}

void printTallyRow(const string& type, uint64_t hit, uint64_t total, size_t indent,
                   size_t typeWidth, size_t countWidth) {
    printIndent(indent);
    std::cout << std::left << std::setw(typeWidth) << type << " : " << std::right << std::fixed
              << std::setprecision(1) << pct(hit, total) << "% (" << std::setw(countWidth) << hit
              << "/" << std::setw(countWidth) << total << ")\n";
}

size_t countWidth(const TypeTally& tally) {
    size_t width = cvtToStr(0).size();
    for (TypeTally::const_iterator it = tally.begin(); it != tally.end(); ++it) {
        width = std::max(width, cvtToStr(it->second.first).size());
        width = std::max(width, cvtToStr(it->second.second).size());
    }
    return width;
}

size_t typeWidth(const TypeTally& tally) {
    size_t typeWidth = 0;
    for (const char* const typep : s_orderedTypes) {
        const string type = typep;
        typeWidth = std::max(typeWidth, type.size());
    }
    for (TypeTally::const_iterator it = tally.begin(); it != tally.end(); ++it) {
        typeWidth = std::max(typeWidth, it->first.size());
    }
    return typeWidth;
}

void printTypeTally(const TypeTally& tally, size_t indent, bool includeMissingOrdered) {
    // Print standard coverage types first for stable output.  When requested,
    // missing standard rows are printed with zero counts for compatibility with
    // the historical flat summary output.
    const size_t typWidth = typeWidth(tally);
    const size_t cntWidth = countWidth(tally);
    for (const char* const typep : s_orderedTypes) {
        const string type = typep;
        const TypeTally::const_iterator it = tally.find(type);
        if (it != tally.end()) {
            printTallyRow(type, it->second.first, it->second.second, indent, typWidth, cntWidth);
        } else if (includeMissingOrdered) {
            printTallyRow(type, 0, 0, indent, typWidth, cntWidth);
        }
    }
    for (TypeTally::const_iterator it = tally.begin(); it != tally.end(); ++it) {
        if (!isOrderedType(it->first)) {
            printTallyRow(it->first, it->second.first, it->second.second, indent, typWidth,
                          cntWidth);
        }
    }
}

}  // namespace

void VlcTop::readCoverage(const string& filename, bool nonfatal) {
    UINFO(2, "readCoverage " << filename);

    std::ifstream is{filename.c_str()};
    if (!is) {
        if (!nonfatal) v3fatal("Can't read coverage file: " << filename);
        return;
    }

    // Testrun and computrons argument unsupported as yet
    VlcTest* const testp = tests().newTest(filename, 0, 0);

    while (!is.eof()) {
        const string line = V3Os::getline(is);
        // UINFO(9, " got " << line);
        if (line[0] == 'C') {
            string::size_type secspace = 3;
            for (; secspace < line.length(); secspace++) {
                if (line[secspace] == '\'' && line[secspace + 1] == ' ') break;
            }
            const string point = line.substr(3, secspace - 3);
            if (!opt.isTypeMatch(point.c_str())) continue;

            const uint64_t hits = std::atoll(line.c_str() + secspace + 1);
            // UINFO(9, "   point '" << point << "'" << " " << hits);

            const uint64_t pointnum = points().findAddPoint(point, hits);
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
    UINFO(2, "writeCoverage " << filename);

    std::ofstream os{filename.c_str()};
    if (!os) {
        v3fatal("Can't write file: " << filename);
        return;
    }

    os << "# SystemC::Coverage-3\n";
    for (const auto& i : m_points) {
        const VlcPoint& point = m_points.pointNumber(i.second);
        os << "C '" << point.name() << "' " << point.count() << '\n';
    }
}

void VlcTop::writeInfo(const string& filename) {
    UINFO(2, "writeInfo " << filename);

    std::ofstream os{filename.c_str()};
    if (!os) {
        v3fatal("Can't write file: " << filename);
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
        int branchesFound = 0;
        int branchesHit = 0;
        for (auto& li : lines) {
            VlcSourceCount& sc = li.second;
            uint64_t daCount = 0;
            std::vector<const VlcPoint*> infoPoints;
            for (const auto& point : sc.points()) {
                if (point->isFsmArc()) continue;
                daCount = std::max(daCount, point->count());
                if (!point->isFsmState()) infoPoints.push_back(point);
            }
            os << "DA:" << sc.lineno() << "," << daCount << "\n";
            if (infoPoints.size() <= 1) continue;
            branchesFound += static_cast<int>(infoPoints.size());
            int point_num = 0;
            for (const VlcPoint* point : infoPoints) {
                os << "BRDA:" << sc.lineno() << ",";
                os << "0,";
                os << point_num << ",";
                os << point->count() << "\n";

                branchesHit += opt.countOk(point->count());
                ++point_num;
            }
        }
        os << "BRF:" << branchesFound << '\n';
        os << "BRH:" << branchesHit << '\n';

        os << "end_of_record\n";
    }
}

//********************************************************************

struct CmpComputrons final {
    bool operator()(const VlcTest* lhsp, const VlcTest* rhsp) const {
        if (lhsp->computrons() != rhsp->computrons()) {
            return lhsp->computrons() < rhsp->computrons();
        }
        return lhsp->bucketsCovered() > rhsp->bucketsCovered();
    }
};

void VlcTop::rank() {
    UINFO(2, "rank...");
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
        if (debug() >= 9) {
            UINFO_PREFIX("Left on iter" << nextrank << ": ");  // LCOV_EXCL_LINE
            remaining.dump();  // LCOV_EXCL_LINE
        }
        VlcTest* bestTestp = nullptr;
        uint64_t bestRemain = 0;
        for (const auto& testp : bytime) {
            if (!testp->rank()) {
                const uint64_t remain = testp->buckets().dataPopCount(remaining);
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

void VlcTop::covergroup() {
    UINFO(2, "covergroup...");
    covergroupCalc();
    if (m_covergroups.empty()) return;
    m_covergroups.dump(std::cout);
}

void VlcTop::covergroupCalc() {
    // Collect covergroup points from all loaded coverage data into m_covergroups
    for (const auto& nameNum : m_points) {
        const VlcPoint& pt = m_points.pointNumber(nameNum.second);
        if (pt.type() != "covergroup") continue;

        const std::string page = pt.page();
        // Page format: "v_covergroup/<cgTypeName>"
        const std::string pagePrefix = "v_covergroup/";
        if (page.size() <= pagePrefix.size()) continue;
        const std::string cgTypeName = page.substr(pagePrefix.size());

        // Parse hier: "<cg_type>.<cp_name>.<bin_name>"
        const std::string hier = pt.hier();
        const size_t dot1 = hier.find('.');
        if (dot1 == std::string::npos) continue;
        const size_t dot2 = hier.find('.', dot1 + 1);
        if (dot2 == std::string::npos) continue;
        const std::string cpName = hier.substr(dot1 + 1, dot2 - dot1 - 1);
        const std::string binName = hier.substr(dot2 + 1);

        VlcCovergroupType& cg
            = m_covergroups.findNewCovergroupType(cgTypeName, pt.filename(), pt.lineno());
        VlcCgCoverpoint& cp = cg.findNewCoverpoint(cpName, pt.isCross());

        // Threshold: use per-bin thresh key (option.at_least) if present, else 1 (SV default)
        const std::string threshStr = pt.thresh();
        const uint64_t binThresh = threshStr.empty() ? 1 : std::stoull(threshStr);
        const uint64_t count = pt.count();
        cp.addBin(binName, pt.binType(), count >= binThresh, count);
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
            UINFO(9, "AnnoCalc count " << filename << ":" << lineno << ":" << point.column() << " "
                                       << point.count() << " " << point.linescov());
            // Base coverage
            source.insertPoint(lineno, &point);
            // Additional lines covered by this statement
            bool range = false;
            int start = 0;
            int end = 0;
            const string linescov = point.linescov();
            for (const char* covp = linescov.c_str(); true; ++covp) {
                if (!*covp || *covp == ',') {  // Ending
                    for (int lni = start; start && lni <= end; ++lni) {
                        source.insertPoint(lni, &point);
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
        // UINFO(1, "Source " << source.name());
        if (opt.annotateAll()) source.needed(true);
        const VlcSource::LinenoMap& lines = source.lines();
        for (auto& li : lines) {
            const VlcSourceCount& sc = li.second;
            // UINFO(0, "Source " << source.name() << ":" << sc.lineno() << ":" << sc.column());
            ++totCases;
            if (opt.countOk(sc.minCount())) {
                ++totOk;
            } else {
                source.needed(true);
            }
        }
    }
    const float pct = totCases ? (100 * totOk / totCases) : 0;
    std::cout << "Annotation Summary:\n";
    std::cout << "  lines with all attached points covered : ";
    std::cout << std::fixed << std::setw(5) << std::setprecision(2) << pct << "%  (" << totOk
              << "/" << totCases << ")\n";
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

        UINFO(1, "annotateOutputFile " << filename << " -> " << outfilename);

        std::ifstream is{filename.c_str()};
        if (!is) {
            v3error("Can't read annotation file: " << filename);
            return;
        }

        std::ofstream os{outfilename.c_str()};
        if (!os) {
            v3error("Can't write file: " << outfilename);
            return;
        }

        os << "//      // verilator_coverage annotation\n";

        int lineno = 0;
        while (!is.eof()) {
            lineno++;
            const std::string line = V3Os::getline(is);

            VlcSource::LinenoMap& lines = source.lines();
            const auto lit = lines.find(lineno);
            if (lit == lines.end()) {
                os << "        " << line << '\n';
            } else {
                VlcSourceCount& sc = lit->second;
                // UINFO(0, "Source " << source.name() << ":" << sc.lineno() << ":" <<
                // sc.column());
                const bool minOk = opt.countOk(sc.minCount());
                const bool maxOk = opt.countOk(sc.maxCount());
                if (minOk) {
                    os << " ";
                } else if (maxOk) {
                    os << "~";
                } else {
                    os << "%";
                }
                os << std::setfill('0') << std::setw(6) << sc.maxCount() << " " << line << '\n';

                if (opt.annotatePoints()) {
                    for (const auto& pit : sc.points()) pit->dumpAnnotate(os, opt.annotateMin());
                }
                bool printedFsmHeader = false;
                for (const auto& pit : sc.points()) {
                    if (!pit->isFsmState() && !pit->isFsmArc()) continue;
                    if (!printedFsmHeader) {
                        os << "        // [FSM coverage]\n";
                        printedFsmHeader = true;
                    }
                    os << (opt.countOk(pit->count()) ? " " : "%");
                    os << std::setfill('0') << std::setw(6) << pit->count() << "        ";
                    if (pit->isFsmState()) {
                        os << "// [fsm_state " << pit->comment() << "]";
                        if (pit->count() == 0) os << " *** UNCOVERED ***";
                        os << "\n";
                    } else if (pit->isFsmDefaultArc()) {
                        os << "// [SYNTHETIC DEFAULT ARC: " << pit->comment() << "]\n";
                    } else {
                        os << "// [fsm_arc " << pit->comment() << "]";
                        if (pit->fsmIsReset() && !opt.includeResetArcs()) {
                            os << " [reset arc, excluded from %]";
                        }
                        os << "\n";
                    }
                }
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

void VlcTop::printTypeSummary() {
    TypeTally tally;
    for (VlcPoints::ByName::value_type& i : m_points) {
        const VlcPoint& pt = m_points.pointNumber(i.second);
        tallyPoint(tally, displayType(pt), pt.count());
    }
    if (tally.empty()) return;
    std::cout << "Coverage Summary:\n";
    // Keep the legacy summary behavior of showing standard coverage types even
    // when the input has no points of that type.
    printTypeTally(tally, s_summaryIndent, true);
}

void VlcTop::printHierarchyReport() {
    std::map<string, TypeTally> hierTallies;
    std::map<string, TypeTally> duTallies;
    bool hasHier = false;
    bool hasCollapsedHier = false;
    for (VlcPoints::ByName::value_type& i : m_points) {
        const VlcPoint& pt = m_points.pointNumber(i.second);
        const string hier = reportHier(pt);
        if (hier.empty()) continue;
        hasHier = true;
        if (isCollapsedHier(hier)) hasCollapsedHier = true;
        const string type = displayType(pt);
        const std::vector<string> parts = splitHier(hier);
        string path;
        for (std::vector<string>::const_iterator it = parts.begin(); it != parts.end(); ++it) {
            path = path.empty() ? *it : path + "." + *it;
            tallyPoint(hierTallies[path], type, pt.count());
        }
        tallyPoint(duTallies[duName(pt)], type, pt.count());
    }

    if (!hasHier) {
        std::cout << "%Warning: --report hierarchy input has no hierarchy fields; "
                  << "printing flat summary instead.\n";
        printTypeSummary();
        return;
    }

    const int levels = opt.reportLevels();
    if (hasCollapsedHier) {
        std::cout << "Note: hierarchy report contains collapsed hierarchy paths; "
                  << "it is not precise per-instance coverage.\n";
    }
    std::cout << "Hierarchy Coverage Summary:\n";
    for (std::map<string, TypeTally>::const_iterator it = hierTallies.begin();
         it != hierTallies.end(); ++it) {
        const std::vector<string> parts = splitHier(it->first);
        if (levels >= 0 && static_cast<int>(parts.size()) > levels + 1) continue;
        printIndent(s_summaryIndent);
        std::cout << it->first << "\n";
        // Hierarchy nodes can be numerous, so only print coverage types present
        // under this node instead of repeating absent zero-count rows.
        printTypeTally(it->second, s_reportRowIndent, false);
    }
    std::cout << "Design Unit Coverage Summary:\n";
    for (std::map<string, TypeTally>::const_iterator it = duTallies.begin(); it != duTallies.end();
         ++it) {
        printIndent(s_summaryIndent);
        std::cout << it->first << "\n";
        // Design-unit summaries follow the hierarchy report style: present
        // types only, but in the same stable order as the flat summary.
        printTypeTally(it->second, s_reportRowIndent, false);
    }
}
