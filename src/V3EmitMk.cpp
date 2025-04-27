// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit Makefile
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3EmitMk.h"

#include "V3EmitCBase.h"
#include "V3HierBlock.h"
#include "V3Os.h"

VL_DEFINE_DEBUG_FUNCTIONS;

// Groups adjacent files in a list, evenly distributing sum of scores
class EmitGroup final {
public:
    struct FileOrConcatenatedFilesList final {
        const std::string m_filename;  // Filename or output group filename if grouping
        std::vector<std::string> m_concatenatedFilenames;  // Grouped filenames if grouping

        bool isConcatenatingFile() const { return !m_concatenatedFilenames.empty(); }
    };

    struct FilenameWithScore final {
        const std::string m_filename;  // Input filename
        const uint64_t m_score;  // Input file complexity
    };

private:
    // Data of a single work unit used in `singleConcatenatedFilesList()`.
    struct WorkList final {
        uint64_t m_totalScore = 0;  // Sum of scores of included files
        std::vector<FilenameWithScore> m_files;  // Included filenames
        int m_bucketsNum
            = 0;  // Number of buckets assigned for this list. Used only in concatenable lists.
        bool m_isConcatenable = true;  // Indicated whether files on this list can be concatenated.
        const int m_dbgId;  // Work list ID for debugging.

        WorkList() = delete;
        explicit WorkList(int id)
            : m_dbgId{id} {}
    };

    // MAIN PARAMETERS

    // Minimum number of input files required to perform concatenation.
    // Concatenation of a small number of files does not give any performance advantages.
    // The value has been chosen arbitrarily, most likely could be larger.
    static constexpr size_t MIN_FILES_COUNT = 16;

    // Concatenation of only a few files most likely does not increase performance.
    // The value has been chosen arbitrarily.
    static constexpr size_t MIN_FILES_PER_BUCKET = 4;

    // MEMBERS

    const std::vector<FilenameWithScore>
        m_inputFiles;  // List of filenames from initial AstCFile list
    std::vector<FileOrConcatenatedFilesList>
        m_outputFiles;  // Output list of files and group files
    const uint64_t m_totalScore;  // Sum of file scores
    const std::string m_groupFilePrefix;  // Prefix for output group filenames
    std::vector<WorkList> m_workLists;  // Lists of small enough files
    std::unique_ptr<std::ofstream> m_logp;  // Dump file
    std::vector<WorkList*> m_concatenableListsByDescSize;  // Lists sorted by size, descending

    EmitGroup(std::vector<FilenameWithScore> inputFiles, uint64_t totalScore,
              std::string groupFilePrefix)
        : m_inputFiles{std::move(inputFiles)}
        , m_totalScore{totalScore}
        , m_groupFilePrefix{groupFilePrefix} {}

    // Debug logging: prints scores histogram
    void dumpLogScoreHistogram(std::ostream& os) {
        constexpr int MAX_BAR_LENGTH = 80;
        constexpr int MAX_INTERVALS_NUM = 60;

        // All scores arranged in ascending order.
        std::vector<uint64_t> sortedScores;
        sortedScores.reserve(m_inputFiles.size());
        std::transform(m_inputFiles.begin(), m_inputFiles.end(), std::back_inserter(sortedScores),
                       [](const FilenameWithScore& inputFile) { return inputFile.m_score; });
        std::sort(sortedScores.begin(), sortedScores.end());

        const int64_t topScore = sortedScores.back();
        os << "Top score: " << topScore << '\n';
        const int maxScoreWidth = std::to_string(topScore).length();

        const int64_t intervalsNum = std::min<int64_t>(topScore + 1, MAX_INTERVALS_NUM);

        struct Interval final {
            uint64_t m_lowerBound = 0;
            int m_size = 0;
        };

        std::vector<Interval> intervals;
        intervals.resize(intervalsNum);

        intervals[0].m_lowerBound = 0;
        for (int i = 1; i < intervalsNum; i++) {
            intervals[i].m_lowerBound = (topScore + 1) * i / intervalsNum + 1;
        }

        for (const uint64_t score : sortedScores) {
            const unsigned int ivIdx = score * intervalsNum / (topScore + 1);
            ++intervals[ivIdx].m_size;
        }

        int topIntervalSize = 0;
        for (const Interval& iv : intervals)
            topIntervalSize = std::max(topIntervalSize, iv.m_size);

        os << "Input files' scores histogram:\n";

        for (const Interval& iv : intervals) {
            const int scaledSize = iv.m_size * (MAX_BAR_LENGTH + 1) / topIntervalSize;
            std::string line = " |" + std::string(scaledSize, '#');

            os << std::setw(maxScoreWidth) << iv.m_lowerBound << line << "  " << iv.m_size << '\n';
        }
        os << std::setw(maxScoreWidth) << (topScore + 1) << '\n';
        os << '\n';
    }

    // PRIVATE METHODS

    // Debug logging: dumps Work Lists and their lists of files
    void dumpWorkLists(std::ostream& os) {
        os << "Initial Work Lists with their concatenation eligibility status:\n";
        for (const WorkList& list : m_workLists) {
            os << "+ [" << (list.m_isConcatenable ? 'x' : ' ') << "] Work List #" << list.m_dbgId
               << "  (num of files: " << list.m_files.size()
               << "; total score: " << list.m_totalScore << ")\n";
            if (debug() >= 6 || list.m_files.size() < 4) {
                // Log all files
                for (const FilenameWithScore& file : list.m_files)
                    os << "| + " << file.m_filename << "  (score: " << file.m_score << ")\n";
            } else {
                // Log only first and last file
                const FilenameWithScore& first = list.m_files.front();
                const FilenameWithScore& last = list.m_files.back();
                os << "| + " << first.m_filename << "  (score: " << first.m_score << ")\n";
                os << "| | (... " << (list.m_files.size() - 2) << " files ...)\n";
                os << "| + " << last.m_filename << "  (score: " << last.m_score << ")\n";
            }
        }
        os << '\n';
    }

    // Debug logging: dumps list of output files. List of grouped files is additionally printed
    // for each concatenating file.
    void dumpOutputList(std::ostream& os) const {
        os << "List of output files after execution of concatenation:\n";

        for (const FileOrConcatenatedFilesList& entry : m_outputFiles) {
            if (entry.isConcatenatingFile()) {
                os << "+ " << entry.m_filename << "  (concatenating file)\n";
                for (const string& f : entry.m_concatenatedFilenames) {
                    os << "| + " << f << '\n';
                }
            } else {
                os << "+ " << entry.m_filename << '\n';
            }
        }
    }

    // Called when the concatenation is aborted, creates an identity mapping
    bool fallbackNoGrouping(size_t inputFilesCount) {
        const int totalBucketsNum = v3Global.opt.outputGroups();
        // Return early if there's nothing to do.
        bool groupingRedundant = false;
        if (inputFilesCount < MIN_FILES_COUNT
            && inputFilesCount <= static_cast<size_t>(totalBucketsNum)) {
            UINFO(4, "File concatenation skipped: Too few files (" << m_inputFiles.size() << " < "
                                                                   << MIN_FILES_COUNT << ")\n");
            groupingRedundant = true;
        }
        if (inputFilesCount < (MIN_FILES_PER_BUCKET * totalBucketsNum)) {
            UINFO(4, "File concatenation skipped: Too few files per bucket ("
                         << m_inputFiles.size() << " < " << MIN_FILES_PER_BUCKET << " - "
                         << totalBucketsNum << ")\n");
            groupingRedundant = true;
        }
        if (!groupingRedundant) return false;

        m_outputFiles.reserve(m_inputFiles.size());
        for (const FilenameWithScore& filename : m_inputFiles) {
            m_outputFiles.push_back({std::move(filename.m_filename), {}});
        }
        return true;
    }

    void createWorkLists() {
        // Create initial Work Lists.

        const int totalBucketsNum = v3Global.opt.outputGroups();
        // Input files with a score exceeding this value are excluded from concatenation.
        const uint64_t concatenableFileMaxScore = m_totalScore / totalBucketsNum / 2;

        V3Stats::addStat("Concatenation max score", concatenableFileMaxScore);
        int nextWorkListId = 0;

        if (m_logp) *m_logp << "Input files with their concatenation eligibility status:\n";
        for (const FilenameWithScore& inputFile : m_inputFiles) {
            const bool fileIsConcatenable = (inputFile.m_score <= concatenableFileMaxScore);
            if (m_logp)
                *m_logp << " + [" << (fileIsConcatenable ? 'x' : ' ') << "] "
                        << inputFile.m_filename << "  (score: " << inputFile.m_score << ")\n";
            V3Stats::addStatSum(fileIsConcatenable ? "Concatenation total grouped score"
                                                   : "Concatenation total non-grouped score",
                                inputFile.m_score);
            // Add new list if the last list's concatenability does not match the inputFile's
            // concatenability
            if (m_workLists.empty() || m_workLists.back().m_isConcatenable != fileIsConcatenable) {
                m_workLists.push_back(WorkList{nextWorkListId++});
                m_workLists.back().m_isConcatenable = fileIsConcatenable;
            }
            // Add inputFile to the last list
            WorkList& list = m_workLists.back();
            list.m_files.push_back({inputFile.m_filename, inputFile.m_score});
            list.m_totalScore += inputFile.m_score;
        }
        if (m_logp) *m_logp << '\n';
    }

    void assignBuckets(uint64_t concatenableFilesTotalScore) {
        // Assign buckets to lists

        const size_t totalBucketsNum = v3Global.opt.outputGroups();

        // More concatenable lists than buckets. Exclude lists with lowest number of files.
        // Does not happen very often due to files being already filtered out by comparison of
        // their score to ConcatenableFilesMaxScore.
        if (m_concatenableListsByDescSize.size() > totalBucketsNum) {
            // Debugging: Log which work lists will be kept
            if (m_logp) {
                *m_logp << "More Work Lists than buckets; "
                           "Work Lists with statuses indicating whether the list will be kept:\n";
                // Only lists that will be kept. List that will be removed are logged below.
                std::for_each(m_concatenableListsByDescSize.begin(),
                              m_concatenableListsByDescSize.begin() + totalBucketsNum,
                              [&](WorkList* listp) {
                                  *m_logp << "+ [x] Work List #" << listp->m_dbgId
                                          << "  (num of files: " << listp->m_files.size()
                                          << "; total score: " << listp->m_totalScore << ")\n";
                              });
            }
            // NOTE: Not just debug logging - notice `isConcatenable` assignment in the loop.
            std::for_each(m_concatenableListsByDescSize.begin() + totalBucketsNum,
                          m_concatenableListsByDescSize.end(), [&](WorkList* listp) {
                              listp->m_isConcatenable = false;

                              if (m_logp)
                                  *m_logp << "+ [ ] Work List #" << listp->m_dbgId
                                          << "  (num of files: " << listp->m_files.size()
                                          << "; total score: " << listp->m_totalScore << ")\n";
                          });
            if (m_logp) *m_logp << '\n';

            m_concatenableListsByDescSize.resize(totalBucketsNum);
            // Recalculate stats
            concatenableFilesTotalScore = 0;
            for (WorkList* listp : m_concatenableListsByDescSize) {
                concatenableFilesTotalScore += listp->m_totalScore;
            }
        }

        const uint64_t idealBucketScore = concatenableFilesTotalScore / totalBucketsNum;

        V3Stats::addStat("Concatenation ideal bucket score", idealBucketScore);

        if (m_logp) *m_logp << "Buckets assigned to Work Lists:\n";
        int availableBuckets = v3Global.opt.outputGroups();
        for (WorkList* listp : m_concatenableListsByDescSize) {
            if (availableBuckets > 0) {
                listp->m_bucketsNum = std::min(
                    availableBuckets, std::max<int>(1, listp->m_totalScore / idealBucketScore));
                availableBuckets -= listp->m_bucketsNum;
                if (m_logp)
                    *m_logp << "+ [" << std::setw(2) << listp->m_bucketsNum << "] Work List #"
                            << listp->m_dbgId << '\n';
            } else {
                // Out of buckets. Instead of recalculating everything just exclude the list.
                listp->m_isConcatenable = false;
                if (m_logp)
                    *m_logp << "+ [ 0] Work List #" << std::left << std::setw(4) << listp->m_dbgId
                            << std::right << " (excluding from concatenation)\n";
            }
        }
        if (m_logp) *m_logp << '\n';
    }

    void buildOutputList() {
        // Assign files to buckets and build final list of files

        // At this point the workLists contains concatenatable file lists separated by one or more
        // non-concatenable file lists. Each concatenatable list has N buckets (where N > 0)
        // assigned to it, which have to be filled with files from this list. Ideally, sum of file
        // scores in every bucket should be the same.
        int concatenatedFileId = 0;
        for (WorkList& list : m_workLists) {
            if (!list.m_isConcatenable) {
                for (FilenameWithScore& file : list.m_files) {
                    m_outputFiles.push_back({std::move(file.m_filename), {}});
                }
                continue;
            }

            // Ideal bucket score limited to buckets and score of the current Work List.
            const uint64_t listIdealBucketScore = list.m_totalScore / list.m_bucketsNum;

            auto fileIt = list.m_files.begin();
            for (int i = 0; i < list.m_bucketsNum; ++i) {
                FileOrConcatenatedFilesList bucket{v3Global.opt.prefix() + "_" + m_groupFilePrefix
                                                       + std::to_string(concatenatedFileId++),
                                                   {}};

                uint64_t bucketScore = 0;

                for (; fileIt != list.m_files.end(); ++fileIt) {
                    const uint64_t diffNow
                        = std::abs((int64_t)(listIdealBucketScore - bucketScore));
                    const uint64_t diffIfAdded = std::abs(
                        (int64_t)(listIdealBucketScore - bucketScore - fileIt->m_score));
                    if (bucketScore == 0 || fileIt->m_score == 0 || diffNow > diffIfAdded) {
                        // Bucket score will be better with the file in it.
                        bucketScore += fileIt->m_score;
                        bucket.m_concatenatedFilenames.push_back(std::move(fileIt->m_filename));
                    } else {
                        // Best possible bucket score reached, process next bucket.
                        break;
                    }
                }

                const bool lastBucketAndLeftovers
                    = (i + 1 == list.m_bucketsNum) && (fileIt != list.m_files.end());
                if (bucket.m_concatenatedFilenames.size() > 1 || lastBucketAndLeftovers) {
                    m_outputFiles.push_back(std::move(bucket));
                } else if (bucket.m_concatenatedFilenames.size() == 1) {
                    // Unwrap the bucket if it contains only one file.
                    m_outputFiles.push_back(
                        {std::move(bucket.m_concatenatedFilenames.front()), {}});
                }
                // Most likely no bucket will be empty in normal situations. If it happen the
                // bucket will just be dropped.
            }
            for (; fileIt != list.m_files.end(); ++fileIt) {
                // The Work List is out of buckets, but some files were left.
                // Add them to the last bucket.
                UASSERT(m_outputFiles.back().isConcatenatingFile(),
                        "Cannot add leftover files to a single file");
                m_outputFiles.back().m_concatenatedFilenames.push_back(fileIt->m_filename);
            }
        }
    }

    void assertFilesSame() const {
        auto ifIt = m_inputFiles.begin();
        auto ofIt = m_outputFiles.begin();
        while (ifIt != m_inputFiles.end() && ofIt != m_outputFiles.end()) {
            if (ofIt->isConcatenatingFile()) {
                for (const string& ocf : ofIt->m_concatenatedFilenames) {
                    UASSERT(ifIt != m_inputFiles.end(),
                            "More output files than input files. First extra file: " << ocf);
                    UASSERT(ifIt->m_filename == ocf,
                            "Name mismatch: " << ifIt->m_filename << " != " << ocf);
                    ++ifIt;
                }
                ++ofIt;
            } else {
                UASSERT(ifIt->m_filename == ofIt->m_filename,
                        "Name mismatch: " << ifIt->m_filename << " != " << ofIt->m_filename);
                ++ifIt;
                ++ofIt;
            }
        }
        UASSERT(ifIt == m_inputFiles.end(),
                "More input files than input files. First extra file: " << ifIt->m_filename);
        UASSERT(ofIt == m_outputFiles.end(),
                "More output files than input files. First extra file: " << ofIt->m_filename);
    }

    void process() {
        UINFO(4, __FUNCTION__ << " group file prefix: " << m_groupFilePrefix << '\n');
        UINFO(5, "Number of input files: " << m_inputFiles.size() << '\n');
        UINFO(5, "Total score: " << m_totalScore << '\n');

        const int totalBucketsNum = v3Global.opt.outputGroups();
        UINFO(5, "Number of buckets: " << totalBucketsNum << '\n');
        UASSERT(totalBucketsNum > 0, "More than 0 buckets required");

        if (fallbackNoGrouping(m_inputFiles.size())) return;

        if (debug() >= 6 || dumpLevel() >= 6) {
            const string filename = v3Global.debugFilename("outputgroup") + ".txt";
            UINFO(5, "Dumping " << filename << endl);
            m_logp = std::unique_ptr<std::ofstream>{V3File::new_ofstream(filename)};
            if (m_logp->fail()) v3fatal("Can't write file: " << filename);
        }

        if (m_logp) dumpLogScoreHistogram(*m_logp);

        createWorkLists();

        // Collect stats and mark lists with only one file as non-concatenable
        size_t concatenableFilesCount = 0;
        int64_t concatenableFilesTotalScore = 0;

        for (WorkList& list : m_workLists) {
            if (!list.m_isConcatenable) continue;

            // "Concatenation" of a single file is pointless
            if (list.m_files.size() == 1) {
                list.m_isConcatenable = false;
                UINFO(5, "Excluding from concatenation: Work List contains only one file: "
                         "Work List #"
                             << list.m_dbgId << endl);
                continue;
            }

            concatenableFilesCount += list.m_files.size();
            concatenableFilesTotalScore += list.m_totalScore;
            // This vector is sorted below
            m_concatenableListsByDescSize.push_back(&list);
        }

        if (m_logp) dumpWorkLists(*m_logp);

        // Check concatenation conditions again using more precise data
        if (fallbackNoGrouping(concatenableFilesCount)) return;

        std::sort(m_concatenableListsByDescSize.begin(), m_concatenableListsByDescSize.end(),
                  [](const WorkList* ap, const WorkList* bp) {
                      // Sort in descending order by number of files
                      if (ap->m_files.size() != bp->m_files.size())
                          return (ap->m_files.size() > bp->m_files.size());
                      // As a fallback sort in ascending order by totalSize. This makes lists
                      // with higher score more likely to be excluded.
                      return bp->m_totalScore > ap->m_totalScore;
                  });

        assignBuckets(concatenableFilesTotalScore);

        buildOutputList();

        if (m_logp) dumpOutputList(*m_logp);
        assertFilesSame();
    }

public:
    static std::vector<FileOrConcatenatedFilesList>
    singleConcatenatedFilesList(std::vector<FilenameWithScore> inputFiles, uint64_t totalScore,
                                const std::string& groupFilePrefix) {
        EmitGroup group{std::move(inputFiles), totalScore, groupFilePrefix};
        group.process();
        return group.m_outputFiles;
    }
};

// ######################################################################
//  Emit statements and expressions

class EmitMk final {
    using FileOrConcatenatedFilesList = EmitGroup::FileOrConcatenatedFilesList;
    using FilenameWithScore = EmitGroup::FilenameWithScore;

    // MEMBERS
    double m_putClassCount = 0;  // Number of classEntries printed

public:
    // METHODS

    static void emitConcatenatingFile(const FileOrConcatenatedFilesList& entry) {
        UASSERT(entry.isConcatenatingFile(), "Passed entry does not represent concatenating file");

        V3OutCFile concatenatingFile{v3Global.opt.makeDir() + "/" + entry.m_filename + ".cpp"};
        concatenatingFile.putsHeader();
        for (const string& file : entry.m_concatenatedFilenames) {
            concatenatingFile.puts("#include \"" + file + ".cpp\"\n");
        }
    }

    void putMakeClassEntry(V3OutMkFile& of, const string& name) {
        of.puts("\t" + V3Os::filenameNonDirExt(name) + " \\\n");
        ++m_putClassCount;
    }

    void emitClassMake() {
        std::vector<FileOrConcatenatedFilesList> vmClassesSlowList;
        std::vector<FileOrConcatenatedFilesList> vmClassesFastList;
        if (v3Global.opt.outputGroups() > 0) {
            std::vector<FilenameWithScore> slowFiles;
            std::vector<FilenameWithScore> fastFiles;
            uint64_t slowTotalScore = 0;
            uint64_t fastTotalScore = 0;

            for (AstNodeFile* nodep = v3Global.rootp()->filesp(); nodep;
                 nodep = VN_AS(nodep->nextp(), NodeFile)) {
                const AstCFile* const cfilep = VN_CAST(nodep, CFile);
                if (cfilep && cfilep->source() && cfilep->support() == false) {
                    std::vector<FilenameWithScore>& files = cfilep->slow() ? slowFiles : fastFiles;
                    uint64_t& totalScore = cfilep->slow() ? slowTotalScore : fastTotalScore;

                    totalScore += cfilep->complexityScore();
                    files.push_back(
                        {V3Os::filenameNonDirExt(cfilep->name()), cfilep->complexityScore()});
                }
            }

            vmClassesSlowList = EmitGroup::singleConcatenatedFilesList(
                std::move(slowFiles), slowTotalScore, "vm_classes_Slow_");
            vmClassesFastList = EmitGroup::singleConcatenatedFilesList(
                std::move(fastFiles), fastTotalScore, "vm_classes_");
        }

        // Generate the makefile
        V3OutMkFile of{v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + "_classes.mk"};
        of.putsHeader();
        of.puts("# DESCR"
                "IPTION: Verilator output: Make include file with class lists\n");
        of.puts("#\n");
        of.puts("# This file lists generated Verilated files, for including "
                "in higher level makefiles.\n");
        of.puts("# See " + v3Global.opt.prefix() + ".mk" + " for the caller.\n");

        of.puts("\n### Switches...\n");
        of.puts("# C11 constructs required?  0/1 (always on now)\n");
        of.puts("VM_C11 = 1\n");
        of.puts("# Timing enabled?  0/1\n");
        of.puts("VM_TIMING = ");
        of.puts(v3Global.usesTiming() ? "1" : "0");
        of.puts("\n");
        of.puts("# Coverage output mode?  0/1 (from --coverage)\n");
        of.puts("VM_COVERAGE = ");
        of.puts(v3Global.opt.coverage() ? "1" : "0");
        of.puts("\n");
        of.puts("# Parallel builds?  0/1 (from --output-split)\n");
        of.puts("VM_PARALLEL_BUILDS = ");
        of.puts(v3Global.useParallelBuild() ? "1" : "0");
        of.puts("\n");
        of.puts("# Tracing output mode?  0/1 (from --trace-fst/--trace-saif/--trace-vcd)\n");
        of.puts("VM_TRACE = ");
        of.puts(v3Global.opt.trace() ? "1" : "0");
        of.puts("\n");
        of.puts("# Tracing output mode in FST format?  0/1 (from --trace-fst)\n");
        of.puts("VM_TRACE_FST = ");
        of.puts(v3Global.opt.traceEnabledFst() ? "1" : "0");
        of.puts("\n");
        of.puts("# Tracing output mode in SAIF format?  0/1 (from --trace-saif)\n");
        of.puts("VM_TRACE_SAIF = ");
        of.puts(v3Global.opt.traceEnabledSaif() ? "1" : "0");
        of.puts("\n");
        of.puts("# Tracing output mode in VCD format?  0/1 (from --trace-vcd)\n");
        of.puts("VM_TRACE_VCD = ");
        of.puts(v3Global.opt.traceEnabledVcd() ? "1" : "0");
        of.puts("\n");

        of.puts("\n### Object file lists...\n");
        for (int support = 0; support < 3; ++support) {
            for (const bool& slow : {false, true}) {
                if (support == 2) {
                    of.puts("# Global classes, need linked once per executable");
                } else if (support) {
                    of.puts("# Generated support classes");
                } else {
                    of.puts("# Generated module classes");
                }
                if (slow) {
                    of.puts(", non-fast-path, compile with low/medium optimization\n");
                } else {
                    of.puts(", fast-path, compile with highest optimization\n");
                }
                const string targetVar = (support == 2   ? "VM_GLOBAL"s
                                          : support == 1 ? "VM_SUPPORT"s
                                                         : "VM_CLASSES"s)
                                         + (slow ? "_SLOW" : "_FAST");
                m_putClassCount = 0;
                of.puts(targetVar + " += \\\n");
                if (support == 2 && v3Global.opt.hierChild()) {
                    // Do nothing because VM_GLOBAL is necessary per executable. Top module will
                    // have them.
                } else if (support == 2 && !slow) {
                    for (const string& cpp : v3Global.verilatedCppFiles())
                        putMakeClassEntry(of, cpp);
                } else if (support == 2 && slow) {
                } else if (support == 0 && v3Global.opt.outputGroups() > 0) {
                    const std::vector<FileOrConcatenatedFilesList>& list
                        = slow ? vmClassesSlowList : vmClassesFastList;
                    for (const FileOrConcatenatedFilesList& entry : list) {
                        if (entry.isConcatenatingFile()) emitConcatenatingFile(entry);
                        putMakeClassEntry(of, entry.m_filename);
                    }
                } else {
                    for (AstNodeFile* nodep = v3Global.rootp()->filesp(); nodep;
                         nodep = VN_AS(nodep->nextp(), NodeFile)) {
                        const AstCFile* const cfilep = VN_CAST(nodep, CFile);
                        if (cfilep && cfilep->source() && cfilep->slow() == (slow != 0)
                            && cfilep->support() == (support != 0)) {
                            putMakeClassEntry(of, cfilep->name());
                        }
                    }
                }
                of.puts("\n");
                V3Stats::addStat("Makefile targets, " + targetVar, m_putClassCount);
            }
        }

        of.puts("\n");
        of.putsHeader();
    }

    void emitOverallMake() {
        // Generate the makefile
        V3OutMkFile of{v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + ".mk"};
        of.putsHeader();
        of.puts("# DESCR"
                "IPTION: Verilator output: "
                "Makefile for building Verilated archive or executable\n");
        of.puts("#\n");
        of.puts("# Execute this makefile from the object directory:\n");
        of.puts("#    make -f " + v3Global.opt.prefix() + ".mk" + "\n");
        of.puts("\n");

        if (v3Global.opt.exe()) {
            of.puts("default: " + v3Global.opt.exeName() + "\n");
        } else if (!v3Global.opt.libCreate().empty()) {
            of.puts("default: lib" + v3Global.opt.libCreate() + "\n");
        } else {
            of.puts("default: lib" + v3Global.opt.prefix() + "\n");
        }
        of.puts("\n### Constants...\n");
        of.puts("# Perl executable (from $PERL, defaults to 'perl' if not set)\n");
        of.puts("PERL = " + V3OutFormatter::quoteNameControls(V3Options::getenvPERL()) + "\n");
        of.puts("# Python3 executable (from $PYTHON3, defaults to 'python3' if not set)\n");
        of.puts("PYTHON3 = " + V3OutFormatter::quoteNameControls(V3Options::getenvPYTHON3())
                + "\n");
        of.puts("# Path to Verilator kit (from $VERILATOR_ROOT)\n");
        of.puts("VERILATOR_ROOT = "
                + V3OutFormatter::quoteNameControls(V3Options::getenvVERILATOR_ROOT()) + "\n");
        of.puts("# SystemC include directory with systemc.h (from $SYSTEMC_INCLUDE)\n");
        of.puts("SYSTEMC_INCLUDE ?= "s + V3Options::getenvSYSTEMC_INCLUDE() + "\n");
        of.puts("# SystemC library directory with libsystemc.a (from $SYSTEMC_LIBDIR)\n");
        of.puts("SYSTEMC_LIBDIR ?= "s + V3Options::getenvSYSTEMC_LIBDIR() + "\n");

        // Only check it if we really need the value
        if (v3Global.opt.systemC() && !V3Options::systemCFound()) {
            v3fatal("Need $SYSTEMC_INCLUDE in environment or when Verilator configured,\n"
                    "and need $SYSTEMC_LIBDIR in environment or when Verilator configured\n"
                    "Probably System-C isn't installed, see http://www.systemc.org\n");
        }

        of.puts("\n### Switches...\n");
        of.puts("# C++ code coverage  0/1 (from --prof-c)\n");
        of.puts("VM_PROFC = "s + ((v3Global.opt.profC()) ? "1" : "0") + "\n");
        of.puts("# SystemC output mode?  0/1 (from --sc)\n");
        of.puts("VM_SC = "s + ((v3Global.opt.systemC()) ? "1" : "0") + "\n");
        of.puts("# Legacy or SystemC output mode?  0/1 (from --sc)\n");
        of.puts("VM_SP_OR_SC = $(VM_SC)\n");
        of.puts("# Deprecated\n");
        of.puts("VM_PCLI = "s + (v3Global.opt.systemC() ? "0" : "1") + "\n");
        of.puts(
            "# Deprecated: SystemC architecture to find link library path (from $SYSTEMC_ARCH)\n");
        of.puts("VM_SC_TARGET_ARCH = "s + V3Options::getenvSYSTEMC_ARCH() + "\n");

        of.puts("\n### Vars...\n");
        of.puts("# Design prefix (from --prefix)\n");
        of.puts("VM_PREFIX = "s + v3Global.opt.prefix() + "\n");
        of.puts("# Module prefix (from --prefix)\n");
        of.puts("VM_MODPREFIX = "s + v3Global.opt.modPrefix() + "\n");

        of.puts("# User CFLAGS (from -CFLAGS on Verilator command line)\n");
        of.puts("VM_USER_CFLAGS = \\\n");
        const std::string solver = V3Options::getenvVERILATOR_SOLVER();
        if (v3Global.useRandomizeMethods() && solver != "")
            of.puts("\t-DVM_SOLVER_DEFAULT='\"" + V3OutFormatter::quoteNameControls(solver)
                    + "\"' \\\n");
        if (!v3Global.opt.libCreate().empty()) of.puts("\t-fPIC \\\n");
        const V3StringList& cFlags = v3Global.opt.cFlags();
        for (const string& i : cFlags) of.puts("\t" + i + " \\\n");
        of.puts("\n");

        of.puts("# User LDLIBS (from -LDFLAGS on Verilator command line)\n");
        of.puts("VM_USER_LDLIBS = \\\n");
        const V3StringList& ldLibs = v3Global.opt.ldLibs();
        for (const string& i : ldLibs) of.puts("\t" + i + " \\\n");
        of.puts("\n");

        V3StringSet dirs;
        of.puts("# User .cpp files (from .cpp's on Verilator command line)\n");
        of.puts("VM_USER_CLASSES = \\\n");
        const V3StringSet& cppFiles = v3Global.opt.cppFiles();
        for (const auto& cppfile : cppFiles) {
            of.puts("\t" + V3Os::filenameNonDirExt(cppfile) + " \\\n");
            const string dir
                = V3Os::filenameRelativePath(V3Os::filenameDir(cppfile), v3Global.opt.makeDir());
            dirs.insert(dir);
        }
        dirs.insert(V3Os::filenameRelativePath(".", v3Global.opt.makeDir()));

        of.puts("\n");

        of.puts("# User .cpp directories (from .cpp's on Verilator command line)\n");
        of.puts("VM_USER_DIR = \\\n");
        for (const auto& i : dirs) of.puts("\t" + i + " \\\n");
        of.puts("\n");

        of.puts("\n### Default rules...\n");
        of.puts("# Include list of all generated classes\n");
        of.puts("include " + v3Global.opt.prefix() + "_classes.mk\n");
        if (v3Global.opt.hierTop()) {
            of.puts("# Include rules for hierarchical blocks\n");
            of.puts("include " + v3Global.opt.prefix() + "_hier.mk\n");
        }
        of.puts("# Include global rules\n");
        of.puts("include $(VERILATOR_ROOT)/include/verilated.mk\n");

        if (v3Global.opt.exe()) {
            of.puts("\n### Executable rules... (from --exe)\n");
            of.puts("VPATH += $(VM_USER_DIR)\n");
            of.puts("\n");
        }

        const string compilerIncludePch
            = v3Global.opt.compilerIncludes().empty() ? "" : "$(VK_PCH_H).fast.gch";
        const string compilerIncludeFlag
            = v3Global.opt.compilerIncludes().empty() ? "" : "$(VK_PCH_I_FAST)";
        for (const string& cppfile : cppFiles) {
            const string basename = V3Os::filenameNonDirExt(cppfile);
            // NOLINTNEXTLINE(performance-inefficient-string-concatenation)
            of.puts(basename + ".o: " + cppfile + " " + compilerIncludePch + "\n");

            // NOLINTNEXTLINE(performance-inefficient-string-concatenation)
            of.puts("\t$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) "
                    + compilerIncludeFlag + " -c -o $@ $<\n");
        }

        if (v3Global.opt.exe()) {
            of.puts("\n### Link rules... (from --exe)\n");
            // let default rule depend on '{prefix}__ALL.a', for compatibility
            of.puts(v3Global.opt.exeName()
                    + ": $(VK_USER_OBJS) $(VK_GLOBAL_OBJS) $(VM_PREFIX)__ALL.a $(VM_HIER_LIBS)\n");
            of.puts("\t$(LINK) $(LDFLAGS) $^ $(LOADLIBES) $(LDLIBS) $(LIBS) $(SC_LIBS) -o $@\n");
            of.puts("\n");
        } else if (!v3Global.opt.libCreate().empty()) {
            const string libCreateDeps = "$(VK_OBJS) $(VK_USER_OBJS) $(VK_GLOBAL_OBJS) "
                                         + v3Global.opt.libCreate() + ".o $(VM_HIER_LIBS)";
            of.puts("\n### Library rules from --lib-create\n");
            // The rule to create .a is defined in verilated.mk, so just define dependency here.
            of.puts(v3Global.opt.libCreateName(false) + ": " + libCreateDeps + "\n");
            of.puts("\n");
            if (v3Global.opt.hierChild()) {
                // Hierarchical child does not need .so because hierTop() will create .so from .a
                of.puts("lib" + v3Global.opt.libCreate() + ": " + v3Global.opt.libCreateName(false)
                        + "\n");
            } else {
                of.puts(v3Global.opt.libCreateName(true) + ": " + libCreateDeps + "\n");
                // Linker on mac emits an error if all symbols are not found here,
                // but some symbols that are referred as "DPI-C" can not be found at this moment.
                // So add dynamic_lookup
                of.puts("ifeq ($(shell uname -s),Darwin)\n");
                of.puts("\t$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -undefined "
                        "dynamic_lookup -shared -flat_namespace -o $@ $^\n");
                of.puts("else\n");
                of.puts(
                    "\t$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -shared -o $@ $^\n");
                of.puts("endif\n");
                of.puts("\n");
                of.puts("lib" + v3Global.opt.libCreate() + ": " + v3Global.opt.libCreateName(false)
                        + " " + v3Global.opt.libCreateName(true) + "\n");
            }
        } else {
            const string libname = "lib" + v3Global.opt.prefix() + ".a";
            of.puts("\n### Library rules (default lib mode)\n");
            // The rule to create .a is defined in verilated.mk, so just define dependency here.
            of.puts(libname + ": $(VK_OBJS) $(VK_USER_OBJS) $(VM_HIER_LIBS)\n");
            of.puts("libverilated.a: $(VK_GLOBAL_OBJS)\n");
            // let default rule depend on '{prefix}__ALL.a', for compatibility
            of.puts("lib" + v3Global.opt.prefix() + ": " + libname
                    + " libverilated.a $(VM_PREFIX)__ALL.a\n");
        }

        of.puts("\n");
        of.putsHeader();
    }

    explicit EmitMk() {
        emitClassMake();
        emitOverallMake();
    }
    virtual ~EmitMk() = default;
};

//######################################################################

class EmitMkHierVerilation final {
    const V3HierBlockPlan* const m_planp;
    const string m_makefile;  // path of this makefile
    void emitCommonOpts(V3OutMkFile& of) const {
        const string cwd = V3Os::filenameRealPath(".");
        of.puts("# Verilation of hierarchical blocks are executed in this directory\n");
        of.puts("VM_HIER_RUN_DIR := " + cwd + "\n");
        of.puts("# Common options for hierarchical blocks\n");
        const string fullpath_bin = V3Os::filenameRealPath(v3Global.opt.buildDepBin());
        const string verilator_wrapper = V3Os::filenameDir(fullpath_bin) + "/verilator";
        of.puts("VM_HIER_VERILATOR := " + verilator_wrapper + "\n");
        of.puts("VM_HIER_INPUT_FILES := \\\n");
        const V3StringList& vFiles = v3Global.opt.vFiles();
        for (const string& i : vFiles) of.puts("\t" + V3Os::filenameRealPath(i) + " \\\n");
        of.puts("\n");
        const V3StringSet& libraryFiles = v3Global.opt.libraryFiles();
        of.puts("VM_HIER_VERILOG_LIBS := \\\n");
        for (const string& i : libraryFiles) {
            of.puts("\t" + V3Os::filenameRealPath(i) + " \\\n");
        }
        of.puts("\n");
    }
    void emitLaunchVerilator(V3OutMkFile& of, const string& argsFile) const {
        of.puts("\t@$(MAKE) -C $(VM_HIER_RUN_DIR) -f " + m_makefile
                + " hier_launch_verilator \\\n");
        of.puts("\t\tVM_HIER_LAUNCH_VERILATOR_ARGSFILE=\"" + argsFile + "\"\n");
    }
    void emit(V3OutMkFile& of) const {
        of.puts("# Hierarchical Verilation -*- Makefile -*-\n");
        of.puts("# DESCR"
                "IPTION: Verilator output: Makefile for hierarchical Verilation\n");
        of.puts("#\n");
        of.puts("# The main makefile " + v3Global.opt.prefix() + ".mk calls this makefile\n");
        of.puts("\n");
        of.puts("ifndef VM_HIER_VERILATION_INCLUDED\n");
        of.puts("VM_HIER_VERILATION_INCLUDED = 1\n\n");

        of.puts(".SUFFIXES:\n");
        of.puts(".PHONY: hier_build hier_verilation hier_launch_verilator\n");

        of.puts("# Libraries of hierarchical blocks\n");
        of.puts("VM_HIER_LIBS := \\\n");
        const V3HierBlockPlan::HierVector blocks
            = m_planp->hierBlocksSorted();  // leaf comes first
        // List in order of leaf-last order so that linker can resolve dependency
        for (const auto& block : vlstd::reverse_view(blocks)) {
            of.puts("\t" + block->hierLibFilename(true) + " \\\n");
        }
        of.puts("\n");

        // Build hierarchical libraries as soon as possible to get maximum parallelism
        of.puts("hier_build: $(VM_HIER_LIBS) " + v3Global.opt.prefix() + ".mk\n");
        of.puts("\t$(MAKE) -f " + v3Global.opt.prefix() + ".mk\n");
        of.puts("hier_verilation: " + v3Global.opt.prefix() + ".mk\n");
        emitCommonOpts(of);

        // Instead of direct execute of "cd $(VM_HIER_RUN_DIR) && $(VM_HIER_VERILATOR)",
        // call via make to get message of "Entering directory" and "Leaving directory".
        // This will make some editors and IDEs happy when viewing a logfile.
        of.puts("# VM_HIER_LAUNCH_VERILATOR_ARGSFILE must be passed as a command argument\n");
        of.puts("hier_launch_verilator:\n");
        of.puts("\t$(VM_HIER_VERILATOR) -f $(VM_HIER_LAUNCH_VERILATOR_ARGSFILE)\n");

        // Top level module
        {
            const string argsFile = v3Global.hierPlanp()->topCommandArgsFilename(false);
            of.puts("\n# Verilate the top module\n");
            of.puts(v3Global.opt.prefix()
                    + ".mk: $(VM_HIER_INPUT_FILES) $(VM_HIER_VERILOG_LIBS) ");
            of.puts(V3Os::filenameNonDir(argsFile) + " ");
            for (const auto& itr : *m_planp) of.puts(itr.second->hierWrapperFilename(true) + " ");
            of.puts("\n");
            emitLaunchVerilator(of, argsFile);
        }

        // Rules to process hierarchical blocks
        of.puts("\n# Verilate hierarchical blocks\n");
        for (const V3HierBlock* const blockp : m_planp->hierBlocksSorted()) {
            const string prefix = blockp->hierPrefix();
            const string argsFilename = blockp->commandArgsFilename(false);
            of.puts(blockp->hierGeneratedFilenames(true));
            of.puts(": $(VM_HIER_INPUT_FILES) $(VM_HIER_VERILOG_LIBS) ");
            of.puts(V3Os::filenameNonDir(argsFilename) + " ");
            const V3HierBlock::HierBlockSet& children = blockp->children();
            for (V3HierBlock::HierBlockSet::const_iterator child = children.begin();
                 child != children.end(); ++child) {
                of.puts((*child)->hierWrapperFilename(true) + " ");
            }
            of.puts("\n");
            emitLaunchVerilator(of, argsFilename);

            // Rule to build lib*.a
            of.puts(blockp->hierLibFilename(true));
            of.puts(": ");
            of.puts(blockp->hierMkFilename(true));
            of.puts(" ");
            for (V3HierBlock::HierBlockSet::const_iterator child = children.begin();
                 child != children.end(); ++child) {
                of.puts((*child)->hierLibFilename(true));
                of.puts(" ");
            }
            of.puts("\n\t$(MAKE) -f " + blockp->hierMkFilename(false) + " -C " + prefix);
            of.puts(" VM_PREFIX=" + prefix);
            of.puts("\n\n");
        }
        of.puts("endif  # Guard\n");
    }

public:
    explicit EmitMkHierVerilation(const V3HierBlockPlan* planp)
        : m_planp{planp}
        , m_makefile{v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + "_hier.mk"} {
        V3OutMkFile of{m_makefile};
        emit(of);
    }
};

//######################################################################
// Gate class functions

void V3EmitMk::emitmk() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    const EmitMk emitter;
}

void V3EmitMk::emitHierVerilation(const V3HierBlockPlan* planp) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    EmitMkHierVerilation{planp};
}
