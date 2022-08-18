// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3File.h"
#include "V3Global.h"
#include "V3Os.h"
#include "V3Stats.h"

#include <iomanip>
#include <map>
#include <unordered_map>

//######################################################################
// Stats dumping

class StatsReport final {
    // TYPES
    using StatColl = std::vector<V3Statistic>;

    // STATE
    std::ofstream& os;  ///< Output stream
    static StatColl s_allStats;  ///< All statistics

    void header() {
        os << "Verilator Statistics Report\n\n";

        os << "Information:\n";
        os << "  " << V3Options::version() << '\n';
        os << "  Arguments: " << v3Global.opt.allArgsString() << '\n';
        os << '\n';
    }

    void sumit() {
        // If sumit is set on a statistic, combine with others of same name
        std::multimap<std::string, V3Statistic*> byName;
        // * is always first
        for (auto& itr : s_allStats) {
            V3Statistic* repp = &itr;
            byName.emplace(repp->name(), repp);
        }

        // Process duplicates
        V3Statistic* lastp = nullptr;
        for (const auto& itr : byName) {
            V3Statistic* repp = itr.second;
            if (lastp && lastp->sumit() && lastp->printit() && lastp->name() == repp->name()
                && lastp->stage() == repp->stage()) {
                repp->combineWith(lastp);
            }
            lastp = repp;
        }
    }

    void stars() {
        // Find all stages
        size_t maxWidth = 0;
        std::multimap<std::string, const V3Statistic*> byName;
        // * is always first
        for (const auto& itr : s_allStats) {
            const V3Statistic* repp = &itr;
            if (repp->stage() == "*" && repp->printit()) {
                if (maxWidth < repp->name().length()) maxWidth = repp->name().length();
                byName.emplace(repp->name(), repp);
            }
        }

        // Print organized by stage
        os << "Global Statistics:\n\n";
        for (const auto& itr : byName) {
            const V3Statistic* repp = itr.second;
            if (repp->perf()) continue;
            os << "  " << std::left << std::setw(maxWidth) << repp->name();
            repp->dump(os);
            os << '\n';
        }
        os << '\n';

        // Print organized by stage
        os << "Performance Statistics:\n\n";
        for (const auto& itr : byName) {
            const V3Statistic* repp = itr.second;
            if (!repp->perf()) continue;
            os << "  " << std::left << std::setw(maxWidth) << repp->name();
            repp->dump(os);
            os << '\n';
        }
        os << '\n';
    }

    void stages() {
        os << "Stage Statistics:\n";

        // Find all stages
        int stage = 0;
        size_t maxWidth = 0;
        std::vector<std::string> stages;
        std::unordered_map<string, int> stageInt;
        std::multimap<std::string, const V3Statistic*> byName;
        // * is always first
        for (auto it = s_allStats.begin(); it != s_allStats.end(); ++it) {
            const V3Statistic* repp = &(*it);
            if (repp->stage() != "*" && repp->printit()) {
                if (maxWidth < repp->name().length()) maxWidth = repp->name().length();
                if (stageInt.find(repp->stage()) == stageInt.end()) {
                    stageInt.emplace(repp->stage(), stage++);
                    stages.push_back(repp->stage());
                }
                byName.emplace(repp->name(), repp);
            }
        }

        // Header
        os << "  Stat     " << std::left << std::setw(maxWidth - 5 - 2) << "";
        for (const string& i : stages) os << "  " << std::left << std::setw(9) << i;
        os << '\n';
        os << "  -------- " << std::left << std::setw(maxWidth - 5 - 2) << "";
        for (auto it = stages.begin(); it != stages.end(); ++it) {
            os << "  " << std::left << std::setw(9) << "-------";
        }
        // os<<endl;

        // Print organized by stage
        string lastName = "__NONE__";
        string lastCommaName = "__NONE__";
        unsigned col = 0;
        for (auto it = byName.cbegin(); it != byName.cend(); ++it) {
            const V3Statistic* repp = it->second;
            if (lastName != repp->name()) {
                lastName = repp->name();
                {
                    string commaName = lastName;
                    string::size_type pos;
                    if ((pos = commaName.find(',')) != string::npos) commaName.erase(pos);
                    if (lastCommaName != commaName) {
                        lastCommaName = commaName;
                        os << '\n';
                    }
                }
                os << '\n';
                col = 0;
                os << "  " << std::left << std::setw(maxWidth) << repp->name();
            }
            while (col < stages.size() && stages.at(col) != repp->stage()) {
                os << std::setw(11) << "";
                col++;
            }
            repp->dump(os);
            col++;
        }
        os << '\n';
    }

public:
    // METHODS
    static void addStat(const V3Statistic& stat) { s_allStats.push_back(stat); }

    // CONSTRUCTORS
    explicit StatsReport(std::ofstream* aofp)
        : os(*aofp) {  // Need () or GCC 4.8 false warning
        header();
        sumit();
        stars();
        stages();
    }
    ~StatsReport() = default;
};

StatsReport::StatColl StatsReport::s_allStats;

//######################################################################
// V3Statstic class

void V3Statistic::dump(std::ofstream& os) const {
    if (perf()) {
        os << "  " << std::right << std::fixed << std::setprecision(6) << std::setw(9) << count();
    } else {
        os << "  " << std::right << std::fixed << std::setprecision(0) << std::setw(9) << count();
    }
}

//######################################################################
// Top Stats class

void V3Stats::addStat(const V3Statistic& stat) { StatsReport::addStat(stat); }

void V3Stats::statsStage(const string& name) {
    static double lastWallTime = -1;
    static int fileNumber = 0;

    const string digitName = V3Global::digitsFilename(++fileNumber) + "_" + name;

    const double wallTime = V3Os::timeUsecs() / 1.0e6;
    if (lastWallTime < 0) lastWallTime = wallTime;
    const double wallTimeDelta = wallTime - lastWallTime;
    lastWallTime = wallTime;
    V3Stats::addStatPerf("Stage, Elapsed time (sec), " + digitName, wallTimeDelta);

    const double memory = V3Os::memUsageBytes() / 1024.0 / 1024.0;
    V3Stats::addStatPerf("Stage, Memory (MB), " + digitName, memory);
}

void V3Stats::statsReport() {
    UINFO(2, __FUNCTION__ << ": " << endl);

    // Open stats file
    const string filename
        = v3Global.opt.hierTopDataDir() + "/" + v3Global.opt.prefix() + "__stats.txt";
    std::ofstream* ofp{V3File::new_ofstream(filename)};
    if (ofp->fail()) v3fatal("Can't write " << filename);

    const StatsReport reporter(ofp);

    // Cleanup
    ofp->close();
    VL_DO_DANGLING(delete ofp, ofp);
}
