// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit Makefile
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2024 by Wilson Snyder. This program is free software; you
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

// ######################################################################
//  Emit statements and expressions

class EmitMk final {
public:
    // METHODS

    struct FileOrConcatenatedFilesList final {
        std::string m_fileName;
        std::vector<std::string> m_concatenatedFileNames{};

        // Concatenating file score for debugTestConcatenation
        std::int64_t m_dbgScore = 0;

        bool isConcatenatingFile() const { return !m_concatenatedFileNames.empty(); }
    };

    struct FilenameWithScore final {
        std::string m_filename;
        std::int64_t m_score;
    };

    // Data of a single work unit used in `singleConcatenatedFilesList()`.
    struct WorkList final {
        std::int64_t m_totalScore = 0;
        std::vector<FilenameWithScore> m_files{};
        // Number of buckets assigned for this list. Used only in concatenable lists.
        int m_bucketsNum = 0;
        // Indicated whether files on this list can be concatenated.
        bool m_isConcatenable = true;
        // Work list ID for debugging.
        const int m_dbgId;

        WorkList() = delete;
        WorkList(int id)
            : m_dbgId{id} {}
    };

    // Debug logging helper: Returns properly indented "* " string.
    // Used as a prefix of log lines representing list entry.
    static std::string logMsgPrefixListEntry(unsigned level, unsigned ancestorsWithStatusNum = 0) {
        UASSERT(level >= ancestorsWithStatusNum,
                "Level must include number of ancestors with status");
        const int spacesNum = ancestorsWithStatusNum * 6 + (level - ancestorsWithStatusNum) * 2;
        const std::string indentSpaces = std::string(spacesNum, ' ');
        return indentSpaces + "* ";
    };

    // Debug logging helper: Returns properly indented "* [+] " if status is true,
    // otherwise "- [ ]". Used as a prefix of log lines representing list entry.
    static std::string logMsgPrefixListEntryWithStatus(bool status, int level,
                                                       int ancestorsWithStatusNum = 0) {
        return logMsgPrefixListEntry(level, ancestorsWithStatusNum) + (status ? "[+] " : "[ ] ");
    };

    // Debug logging: prints scores histogram
    static void debugLogScoreHistogram(const std::vector<std::int64_t>& sortedScores) {
        constexpr int LOG_LEVEL = 6;

        if (debug() < LOG_LEVEL) return;

        constexpr int MAX_BAR_LENGTH = 80;
        constexpr int MAX_INTERVALS_NUM = 60;

        const auto topScore = sortedScores.back();
        UINFO(LOG_LEVEL, "Top score: " << topScore << endl);
        const int maxScoreWidth = topScore < 10       ? 1
                                  : topScore < 100    ? 2
                                  : topScore < 1000   ? 3
                                  : topScore < 10000  ? 4
                                  : topScore < 100000 ? 5
                                                      : 7;

        const int intervalsNum = std::min<int>(topScore + 1, MAX_INTERVALS_NUM);
        const double intervalWidth = double(topScore + 1) / intervalsNum;

        struct Interval final {
            int64_t m_lowerBound = 0;
            int m_size = 0;
        };

        std::vector<Interval> intervals;
        intervals.resize(intervalsNum);

        for (int64_t score = topScore; score >= 0; --score) {
            const int ivIdx = int(int64_t(score) / intervalWidth);
            intervals[ivIdx].m_lowerBound = int64_t(score);
        }

        for (const auto score : sortedScores) {
            const int ivIdx = int((score) / intervalWidth);
            intervals[ivIdx].m_size += 1;
        }

        int topIntervalSize = 0;
        for (const auto& iv : intervals) topIntervalSize = std::max(topIntervalSize, iv.m_size);

        UINFO(LOG_LEVEL, "Input files' scores histogram:" << endl);

        const double barLenToIvSizeRatio = double(MAX_BAR_LENGTH + 1) / topIntervalSize;
        for (int ivIdx = 0; ivIdx < intervalsNum; ++ivIdx) {
            const auto iv = intervals[ivIdx];
            const std::array<std::string, 9> barChars
                = {" ",
                   // Block characters, from "left one eight block" to "full block"
                   "\u258E", "\u258E", "\u258D", "\u258C", "\u258B", "\u258A", "\u2589", "\u2588"};
            const auto scaledSize
                = int(std::round(iv.m_size * barLenToIvSizeRatio * barChars.size()));

            std::string line = " |";
            for (int i = 0; i < int(scaledSize / barChars.size()); ++i) line += barChars.back();
            line += barChars[scaledSize % barChars.size()];

            UINFO(LOG_LEVEL, std::setw(maxScoreWidth)
                                 << iv.m_lowerBound << line << "  " << iv.m_size << endl);
        }
        UINFO(LOG_LEVEL, std::setw(maxScoreWidth) << (topScore + 1) << endl);
    }

    // Debug logging: prints Work Lists and their lists of files
    static void debugLogWorkLists(const std::vector<WorkList>& workLists) {
        constexpr int LOG_LEVEL = 5;

        if (debug() < LOG_LEVEL) return;

        UINFO(5, "Initial Work Lists with their concatenation eligibility status:" << endl);
        for (const auto& list : workLists) {
            UINFO(5, logMsgPrefixListEntryWithStatus(list.m_isConcatenable, 0)
                         << "Work List #" << list.m_dbgId << "  ("
                         << "num of files: " << list.m_files.size() << "; "
                         << "total score: " << list.m_totalScore << ")" << endl);
            if (debug() >= 6) {
                // Log all files
                for (const auto& file : list.m_files)
                    UINFO(6, logMsgPrefixListEntry(1, 1)
                                 << file.m_filename << "  ("
                                 << "score: " << file.m_score << ")" << endl);
            } else {
                // Log only first and last file
                if (list.m_files.size() > 3) {
                    const auto& first = list.m_files.front();
                    const auto& last = list.m_files.back();
                    UINFO(5, logMsgPrefixListEntry(1, 1)
                                 << first.m_filename << "  ("
                                 << "score: " << first.m_score << ")" << endl);
                    UINFO(5, logMsgPrefixListEntry(1, 1)
                                 << "(... " << (list.m_files.size() - 2) << " files ...)" << endl);
                    UINFO(5, logMsgPrefixListEntry(1, 1)
                                 << last.m_filename << "  ("
                                 << "score: " << last.m_score << ")" << endl);
                } else {
                    // Print full list, as it is as long or shorter than abbreviated list.
                    for (const auto& file : list.m_files)
                        UINFO(5, logMsgPrefixListEntry(1)
                                     << file.m_filename << "  ("
                                     << "score: " << file.m_score << ")" << endl);
                }
            }
        }
    }

    // Debug logging: prints list of output files. List of grouped files is additionally printed
    // for each concatenating file.
    static void
    debugLogOutputFilesList(const std::vector<FileOrConcatenatedFilesList>& outputFiles,
                            bool logToStdOut = false) {
        constexpr int LOG_LEVEL = 5;

        if (!logToStdOut && debug() < LOG_LEVEL) return;

        std::stringstream line;

// Prints to stdout or debug log, depending on value of `logToStdOut`.
#define DEBUG_LOG_OUTPUT_FILE_LIST_MSG(stmt) \
    line << stmt; \
    if (!logToStdOut) \
        UINFO(LOG_LEVEL, line.str()); \
    else \
        std::cout << line.str(); \
    line.str(std::string{});

        DEBUG_LOG_OUTPUT_FILE_LIST_MSG(
            "List of output files after execution of concatenation:" << endl);

        for (const auto& entry : outputFiles) {
            if (entry.isConcatenatingFile()) {
                DEBUG_LOG_OUTPUT_FILE_LIST_MSG(logMsgPrefixListEntry(0)
                                               << entry.m_fileName
                                               << "  (concatenating file; total score: "
                                               << entry.m_dbgScore << ")" << endl);
                for (const auto& f : entry.m_concatenatedFileNames) {
                    DEBUG_LOG_OUTPUT_FILE_LIST_MSG(logMsgPrefixListEntry(1) << f << endl);
                }
            } else {
                DEBUG_LOG_OUTPUT_FILE_LIST_MSG(logMsgPrefixListEntry(0)
                                               << entry.m_fileName << endl);
            }
        }

#undef DEBUG_LOG_OUTPUT_FILE_LIST_MSG
    }

    static void
    checkInputAndOutputListsEquality(const std::vector<FilenameWithScore>& inputFiles,
                                     const std::vector<FileOrConcatenatedFilesList>& outputFiles) {
        auto ifIt = inputFiles.begin();
        auto ofIt = outputFiles.begin();
        while (ifIt != inputFiles.end() && ofIt != outputFiles.end()) {
            if (ofIt->isConcatenatingFile()) {
                for (const auto& ocf : ofIt->m_concatenatedFileNames) {
                    UASSERT(ifIt != inputFiles.end(),
                            "More output files than input files. First extra file: " << ocf);
                    UASSERT(ifIt->m_filename == ocf,
                            "Name mismatch: " << ifIt->m_filename << " != " << ocf);
                    ++ifIt;
                }
                ++ofIt;
            } else {
                UASSERT(ifIt->m_filename == ofIt->m_fileName,
                        "Name mismatch: " << ifIt->m_filename << " != " << ofIt->m_fileName);
                ++ifIt;
                ++ofIt;
            }
        }
        UASSERT(ifIt == inputFiles.end(),
                "More input files than input files. First extra file: " << ifIt->m_filename);
        UASSERT(ofIt == outputFiles.end(),
                "More output files than input files. First extra file: " << ofIt->m_fileName);
    }

    static std::vector<FileOrConcatenatedFilesList>
    singleConcatenatedFilesList(std::vector<FilenameWithScore> inputFiles, std::int64_t totalScore,
                                std::string concatenatingFilePrefix) {
        UINFO(4, __FUNCTION__ << ":" << endl);
        UINFO(5, "Number of input files: " << inputFiles.size() << endl);
        UINFO(5, "Total score: " << totalScore << endl);
        UINFO(5, "Concatenated file prefix: " << concatenatingFilePrefix << endl);

        // Called when the concatenation is aborted
        static const auto convertInputFilesToOutputFiles
            = [](std::vector<FilenameWithScore> inputFiles) {
                  std::vector<FileOrConcatenatedFilesList> outputFiles;
                  outputFiles.reserve(inputFiles.size());
                  for (auto& file : inputFiles) {
                      outputFiles.push_back({/*fileName=*/std::move(file.m_filename)});
                  }
                  return outputFiles;
              };

        const int totalBucketsNum = v3Global.opt.outputGroups();
        UINFO(5, "Number of buckets: " << totalBucketsNum << endl);
        UASSERT(totalBucketsNum > 0, "More than 0 buckets required");

        // MAIN PARAMETERS

        // Minimum number of input files required to perform concatenation.
        // Concatenation of a small number of files does not give any performance advantages.
        // The value has been chosen arbitrarily, most likely could be larger.
        constexpr std::size_t MIN_FILES_COUNT = 100;

        // Concatenation of only a few files most likely does not increase performance.
        // The value has been chosen arbitrarily.
        constexpr std::size_t MIN_FILES_PER_BUCKET = 4;

        // ---

        {
            // Return early if there's nothing to do.
            bool returnEarly = false;
            if (inputFiles.size() < MIN_FILES_COUNT) {
                UINFO(0, "File concatenation skipped: Too few files ("
                             << inputFiles.size() << " < " << MIN_FILES_COUNT << ")" << endl);
                returnEarly = true;
            }
            if (inputFiles.size() < (MIN_FILES_PER_BUCKET * totalBucketsNum)) {
                UINFO(0, "File concatenation skipped: Too few files per bucket ("
                             << inputFiles.size() << " < " << MIN_FILES_PER_BUCKET << " - "
                             << totalBucketsNum << ")" << endl);
                returnEarly = true;
            }
            if (returnEarly) return convertInputFilesToOutputFiles(std::move(inputFiles));
        }

        // Calculate score threshold for filtering out upper outliers.

        // All scores arranged in ascending order.
        std::vector<std::int64_t> sortedScores;
        sortedScores.reserve(inputFiles.size());
        std::transform(inputFiles.begin(), inputFiles.end(), std::back_inserter(sortedScores),
                       [](const FilenameWithScore& inputFile) { return inputFile.m_score; });
        std::sort(sortedScores.begin(), sortedScores.end());

        debugLogScoreHistogram(sortedScores);

        // Input files with a score exceeding this value are excluded from concatenation.
        const std::int64_t concatenableFileMaxScore = totalScore / totalBucketsNum / 2;

        UINFO(5, "Concatenable file max score: " << concatenableFileMaxScore << endl);

        // Create initial Work Lists.

        std::vector<WorkList> workLists{};
        int nextWorkListId = 0;

        UINFO(6, "Input files with their concatenation eligibility status:" << endl);
        for (const auto& inputFile : inputFiles) {
            const bool fileIsConcatenable = (inputFile.m_score <= concatenableFileMaxScore);
            UINFO(6, logMsgPrefixListEntryWithStatus(fileIsConcatenable, 0)
                         << inputFile.m_filename << "  ("
                         << "score: " << inputFile.m_score << ")" << endl);
            // Add new list if the last list's concatenability does not match the inputFile's
            // concatenability
            if (workLists.empty() || workLists.back().m_isConcatenable != fileIsConcatenable) {
                workLists.push_back(WorkList{nextWorkListId++});
                workLists.back().m_isConcatenable = fileIsConcatenable;
            }
            // Add inputFile to the last list
            auto& list = workLists.back();
            list.m_files.push_back({inputFile.m_filename, inputFile.m_score});
            list.m_totalScore += inputFile.m_score;
        }

        // Collect stats and mark lists with only one file as non-concatenable

        std::size_t concatenableFilesCount = 0;
        std::int64_t concatenableFilesTotalScore = 0;
        std::size_t concatenableFilesListsCount = 0;

        std::vector<WorkList*> concatenableListsByDescSize;

        for (auto& list : workLists) {
            if (!list.m_isConcatenable) continue;

            // "Concatenation" of a single file is pointless
            if (list.m_files.size() == 1) {
                list.m_isConcatenable = false;
                UINFO(5, "Excluding from concatenation: Work List contains only one file: "
                             << "Work List #" << list.m_dbgId << endl);
                continue;
            }

            concatenableFilesCount += list.m_files.size();
            concatenableFilesTotalScore += list.m_totalScore;
            ++concatenableFilesListsCount;
            // This vector is sorted below
            concatenableListsByDescSize.push_back(&list);
        }

        debugLogWorkLists(workLists);

        {
            // Check concatenation conditions again using more precise data
            bool returnEarly = false;
            if (concatenableFilesCount < MIN_FILES_COUNT) {
                UINFO(0, "File concatenation skipped: Too few files ("
                             << concatenableFilesCount << " < " << MIN_FILES_COUNT << ")" << endl);
                returnEarly = true;
            }
            if (concatenableFilesCount < (MIN_FILES_PER_BUCKET * totalBucketsNum)) {
                UINFO(0, "File concatenation skipped: Too few files per bucket ("
                             << concatenableFilesCount << " < " << MIN_FILES_PER_BUCKET << " * "
                             << totalBucketsNum << ")" << endl);
                returnEarly = true;
            }
            if (returnEarly) return convertInputFilesToOutputFiles(std::move(inputFiles));
        }

        std::sort(concatenableListsByDescSize.begin(), concatenableListsByDescSize.end(),
                  [](const WorkList* ap, const WorkList* bp) {
                      // Sort in descending order by number of files
                      if (ap->m_files.size() != bp->m_files.size())
                          return (ap->m_files.size() > bp->m_files.size());
                      // As a fallback sort in ascending order by totalSize. This makes lists
                      // with higher score more likely to be excluded.
                      return bp->m_totalScore > ap->m_totalScore;
                  });

        // Assign buckets to lists

        // More concatenable lists than buckets. Exclude lists with lowest number of files.
        // Does not happen very often due to files being already filtered out by comparison of
        // their score to ConcatenableFilesMaxScore.
        if (concatenableFilesListsCount > static_cast<std::size_t>(totalBucketsNum)) {
            // Debugging: Log which work lists will be kept
            if (debug() >= 5) {
                UINFO(5,
                      "More Work Lists than buckets; "
                          << "Work Lists with statuses indicating whether the list will be kept:"
                          << endl);
                // Only lists that will be kept. List that will be removed are logged below.
                std::for_each(
                    concatenableListsByDescSize.begin(),
                    concatenableListsByDescSize.begin() + totalBucketsNum, [](auto* listp) {
                        UINFO(5, logMsgPrefixListEntryWithStatus(true, 0)
                                     << "Work List #" << listp->m_dbgId << "  ("
                                     << "num of files: " << listp->m_files.size() << "; "
                                     << "total score: " << listp->m_totalScore << ")" << endl);
                    });
            }
            // NOTE: Not just debug logging - notice `isConcatenable` assignment in the loop.
            std::for_each(concatenableListsByDescSize.begin() + totalBucketsNum,
                          concatenableListsByDescSize.end(), [](auto* listp) {
                              listp->m_isConcatenable = false;

                              UINFO(5, logMsgPrefixListEntryWithStatus(false, 0)
                                           << "Work List #" << listp->m_dbgId << "  ("
                                           << "num of files: " << listp->m_files.size() << "; "
                                           << "total score: " << listp->m_totalScore << ")"
                                           << endl);
                          });

            concatenableListsByDescSize.resize(totalBucketsNum);
            concatenableFilesListsCount = totalBucketsNum;
            // Recalculate stats
            concatenableFilesCount = 0;
            concatenableFilesTotalScore = 0;
            for (auto* listp : concatenableListsByDescSize) {
                concatenableFilesCount += listp->m_files.size();
                concatenableFilesTotalScore += listp->m_totalScore;
            }
        }

        const std::int64_t idealBucketScore = concatenableFilesTotalScore / totalBucketsNum;

        UINFO(5, "Number of buckets: " << totalBucketsNum << endl);
        UINFO(5, "Ideal bucket score: " << idealBucketScore << endl);

        UINFO(5, "Buckets assigned to Work Lists:" << endl);
        int availableBuckets = totalBucketsNum;
        for (auto* listp : concatenableListsByDescSize) {
            if (availableBuckets > 0) {
                listp->m_bucketsNum = std::min<int>(
                    availableBuckets, std::max<int>(1, listp->m_totalScore / idealBucketScore));
                availableBuckets -= listp->m_bucketsNum;
                UINFO(5, logMsgPrefixListEntry(0)
                             << "[" << std::setw(2) << listp->m_bucketsNum << "] "
                             << "Work List #" << listp->m_dbgId << endl);
            } else {
                // Out of buckets. Instead of recalculating everything just exclude the list.
                listp->m_isConcatenable = false;
                UINFO(5, logMsgPrefixListEntry(0) << "[ 0] "
                                                  << "Work List #" << std::left << std::setw(4)
                                                  << listp->m_dbgId << std::right << " "
                                                  << "(excluding from concatenation)" << endl);
            }
        }

        // Assign files to buckets and build final list of files

        std::vector<FileOrConcatenatedFilesList> outputFiles;

        // At this point the workLists contains concatenatable file lists separated by one or more
        // non-concatenable file lists. Each concatenatable list has N buckets (where N > 0)
        // assigned to it, which have to be filled with files from this list. Ideally, sum of file
        // scores in every bucket should be the same.
        int concatenatedFileId = 0;
        for (auto& list : workLists) {
            if (!list.m_isConcatenable) {
                for (auto& file : list.m_files) {
                    FileOrConcatenatedFilesList e{};
                    e.m_fileName = std::move(file.m_filename);
                    outputFiles.push_back(std::move(e));
                }
                continue;
            }

            // Ideal bucket score limited to buckets and score of the current Work List.
            const std::int64_t listIdealBucketScore = list.m_totalScore / list.m_bucketsNum;

            auto fileIt = list.m_files.begin();
            for (int i = 0; i < list.m_bucketsNum; ++i) {
                FileOrConcatenatedFilesList bucket;
                std::int64_t bucketScore = 0;

                bucket.m_fileName = concatenatingFilePrefix + std::to_string(concatenatedFileId);
                ++concatenatedFileId;

                for (; fileIt != list.m_files.end(); ++fileIt) {
                    auto diffNow = std::abs(listIdealBucketScore - bucketScore);
                    auto diffIfAdded
                        = std::abs(listIdealBucketScore - bucketScore - fileIt->m_score);
                    if (bucketScore == 0 || fileIt->m_score == 0 || diffNow > diffIfAdded) {
                        // Bucket score will be better with the file in it.
                        bucketScore += fileIt->m_score;
                        bucket.m_concatenatedFileNames.push_back(std::move(fileIt->m_filename));
                    } else {
                        // Best possible bucket score reached, process next bucket.
                        break;
                    }
                }

                if (bucket.m_concatenatedFileNames.size() == 1) {
                    // Unwrap the bucket if it contains only one file.
                    FileOrConcatenatedFilesList file;
                    file.m_fileName = bucket.m_concatenatedFileNames.front();
                    outputFiles.push_back(std::move(file));
                } else if (bucket.m_concatenatedFileNames.size() > 1) {
                    bucket.m_dbgScore = bucketScore;
                    outputFiles.push_back(std::move(bucket));
                }
                // Most likely no bucket will be empty in normal situations. If it happen the
                // bucket will just be dropped.
            }
            for (; fileIt != list.m_files.end(); ++fileIt) {
                // The Work List is out of buckets, but some files were left.
                // Add them to the last bucket.
                outputFiles.back().m_concatenatedFileNames.push_back(fileIt->m_filename);
            }
        }

        debugLogOutputFilesList(outputFiles);
        checkInputAndOutputListsEquality(inputFiles, outputFiles);

        return outputFiles;
    }

    static void emitConcatenatingFile(const FileOrConcatenatedFilesList& entry) {
        UASSERT(entry.isConcatenatingFile(), "Passed entry does not represent concatenating file");

        V3OutCFile concatenatingFile{v3Global.opt.makeDir() + "/" + entry.m_fileName + ".cpp"};
        concatenatingFile.putsHeader();
        for (const auto& file : entry.m_concatenatedFileNames) {
            concatenatingFile.puts("#include \"" + file + ".cpp\"\n");
        }
    }

    void putMakeClassEntry(V3OutMkFile& of, const string& name) {
        of.puts("\t" + V3Os::filenameNonDirExt(name) + " \\\n");
    }

    void emitClassMake() {
        std::vector<FileOrConcatenatedFilesList> vmClassesSlowList{};
        std::vector<FileOrConcatenatedFilesList> vmClassesFastList{};
        if (v3Global.opt.outputGroups() > 0) {
            std::vector<FilenameWithScore> slowFiles{};
            std::vector<FilenameWithScore> fastFiles{};
            std::int64_t slowTotalScore = 0;
            std::int64_t fastTotalScore = 0;

            for (AstNodeFile* nodep = v3Global.rootp()->filesp(); nodep;
                 nodep = VN_AS(nodep->nextp(), NodeFile)) {
                const AstCFile* const cfilep = VN_CAST(nodep, CFile);
                if (cfilep && cfilep->source() && cfilep->support() == false) {
                    auto& files = cfilep->slow() ? slowFiles : fastFiles;
                    auto& totalScore = cfilep->slow() ? slowTotalScore : fastTotalScore;

                    FilenameWithScore f;
                    f.m_filename = V3Os::filenameNonDirExt(cfilep->name());
                    f.m_score = cfilep->complexityScore();

                    totalScore += f.m_score;
                    files.push_back(std::move(f));
                }
            }

            vmClassesSlowList = singleConcatenatedFilesList(std::move(slowFiles), slowTotalScore,
                                                            "vm_classes_slow_");
            vmClassesFastList = singleConcatenatedFilesList(std::move(fastFiles), fastTotalScore,
                                                            "vm_classes_fast_");
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
        of.puts("# Tracing output mode?  0/1 (from --trace/--trace-fst)\n");
        of.puts("VM_TRACE = ");
        of.puts(v3Global.opt.trace() ? "1" : "0");
        of.puts("\n");
        of.puts("# Tracing output mode in VCD format?  0/1 (from --trace)\n");
        of.puts("VM_TRACE_VCD = ");
        of.puts(v3Global.opt.trace() && v3Global.opt.traceFormat().vcd() ? "1" : "0");
        of.puts("\n");
        of.puts("# Tracing output mode in FST format?  0/1 (from --trace-fst)\n");
        of.puts("VM_TRACE_FST = ");
        of.puts(v3Global.opt.trace() && v3Global.opt.traceFormat().fst() ? "1" : "0");
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
                of.puts(support == 2 ? "VM_GLOBAL" : support == 1 ? "VM_SUPPORT" : "VM_CLASSES");
                of.puts(slow ? "_SLOW" : "_FAST");
                of.puts(" += \\\n");
                if (support == 2 && v3Global.opt.hierChild()) {
                    // Do nothing because VM_GLOBAL is necessary per executable. Top module will
                    // have them.
                } else if (support == 2 && !slow) {
                    putMakeClassEntry(of, "verilated.cpp");
                    if (v3Global.dpi()) putMakeClassEntry(of, "verilated_dpi.cpp");
                    if (v3Global.opt.vpi()) putMakeClassEntry(of, "verilated_vpi.cpp");
                    if (v3Global.opt.savable()) putMakeClassEntry(of, "verilated_save.cpp");
                    if (v3Global.opt.coverage()) putMakeClassEntry(of, "verilated_cov.cpp");
                    if (v3Global.opt.trace()) {
                        putMakeClassEntry(of, v3Global.opt.traceSourceBase() + "_c.cpp");
                    }
                    if (v3Global.usesProbDist()) putMakeClassEntry(of, "verilated_probdist.cpp");
                    if (v3Global.usesTiming()) putMakeClassEntry(of, "verilated_timing.cpp");
                    if (v3Global.useRandomizeMethods())
                        putMakeClassEntry(of, "verilated_random.cpp");
                    putMakeClassEntry(of, "verilated_threads.cpp");
                    if (v3Global.opt.usesProfiler()) {
                        putMakeClassEntry(of, "verilated_profiler.cpp");
                    }
                } else if (support == 2 && slow) {
                } else if ((support == 0) && (v3Global.opt.outputGroups() > 0)) {
                    const auto& list = slow ? vmClassesSlowList : vmClassesFastList;
                    for (const auto& entry : list) {
                        if (entry.isConcatenatingFile()) { emitConcatenatingFile(entry); }
                        putMakeClassEntry(of, entry.m_fileName);
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
            const string dir = V3Os::filenameDir(cppfile);
            dirs.insert(dir);
        }
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

void V3EmitMk::debugTestConcatenation(const char* inputFile) {
    const std::unique_ptr<std::ifstream> ifp{V3File::new_ifstream_nodepend(inputFile)};
    std::vector<EmitMk::FilenameWithScore> inputList;
    std::int64_t totalScore = 0;

    EmitMk::FilenameWithScore current{};
    while ((*ifp) >> current.m_score >> std::ws) {
        char ch;
        while (ch = ifp->get(), ch && ch != ' ' && ch != '\t' && ch != '\n' && ch != '\r') {
            current.m_filename.push_back(ch);
        }
        totalScore += current.m_score;
        inputList.push_back(std::move(current));
        current = EmitMk::FilenameWithScore{};
    }

    const std::vector<EmitMk::FileOrConcatenatedFilesList> list
        = EmitMk::singleConcatenatedFilesList(std::move(inputList), totalScore,
                                              "concatenating_file_");

    EmitMk::debugLogOutputFilesList(list, true);
}

void V3EmitMk::emitmk() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    const EmitMk emitter;
}

void V3EmitMk::emitHierVerilation(const V3HierBlockPlan* planp) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    EmitMkHierVerilation{planp};
}
