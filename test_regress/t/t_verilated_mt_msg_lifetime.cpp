// -*- mode: C++; c-file-style: "cc-mode" -*-
// DESCRIPTION: Verilator: MT message wrappers copy string arguments
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#include "verilated.h"
#define VERILATOR_VERILATED_CPP_
#include "verilated_imp.h"

#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

double sc_time_stamp() { return 0.0; }

struct MessageRecord final {
    const bool filenameNull;
    const int line;
    const bool hierNull;
    const bool messageNull;
    const std::string filename;
    const std::string hier;
    const std::string message;

    MessageRecord(const char* filenamep, int linenum, const char* hierp, const char* messagep)
        : filenameNull{!filenamep}
        , line{linenum}
        , hierNull{!hierp}
        , messageNull{!messagep}
        , filename{filenamep ? filenamep : ""}
        , hier{hierp ? hierp : ""}
        , message{messagep ? messagep : ""} {}
};

static std::vector<MessageRecord> s_finishRecords;
static std::vector<MessageRecord> s_stopRecords;
static std::vector<MessageRecord> s_fatalRecords;
static std::vector<MessageRecord> s_warnRecords;

void vl_finish(const char* filenamep, int linenum, const char* hierp) {
    s_finishRecords.emplace_back(filenamep, linenum, hierp, nullptr);
}

void vl_stop(const char* filenamep, int linenum, const char* hierp) {
    s_stopRecords.emplace_back(filenamep, linenum, hierp, nullptr);
}

void vl_fatal(const char* filenamep, int linenum, const char* hierp, const char* messagep) {
    s_fatalRecords.emplace_back(filenamep, linenum, hierp, messagep);
}

void vl_warn(const char* filenamep, int linenum, const char* hierp, const char* messagep) {
    s_warnRecords.emplace_back(filenamep, linenum, hierp, messagep);
}

static void fail(const std::string& text) {
    std::cerr << "%Error: " << text << '\n';
    std::abort();
}

static void checkRecord(const MessageRecord& record, int line, bool filenameNull,
                        const std::string& filename, bool hierNull, const std::string& hier,
                        bool messageNull, const std::string& message) {
    if (record.line != line) fail("line mismatch");
    if (record.filenameNull != filenameNull) fail("filename nullness mismatch");
    if (record.filename != filename) fail("filename mismatch");
    if (record.hierNull != hierNull) fail("hierarchy nullness mismatch");
    if (record.hier != hier) fail("hierarchy mismatch");
    if (record.messageNull != messageNull) fail("message nullness mismatch");
    if (record.message != message) fail("message mismatch");
}

static std::string longString(const char* prefix, char fill, const char* suffix = "") {
    return std::string{prefix} + std::string(512, fill) + suffix;
}

static void queueWarning() {
    const std::string filename = longString("mt_msg_lifetime_warn_source_", 'w', ".sv");
    const std::string hier = longString("mt_msg_lifetime_warn_hier_", 'h');
    const std::string message = longString("mt_msg_lifetime_warn_message_", 'm');
    VL_WARN_MT(filename.c_str(), 122, hier.c_str(), message.c_str());
    VL_WARN_MT("", 172, "", "");
    VL_WARN_MT(nullptr, 222, nullptr, nullptr);
}

static void queueFinish() {
    const std::string filename = longString("mt_msg_lifetime_finish_source_", 'f', ".sv");
    const std::string hier = longString("mt_msg_lifetime_finish_hier_", 'h');
    VL_FINISH_MT(filename.c_str(), 123, hier.c_str());
    VL_FINISH_MT("", 173, "");
    VL_FINISH_MT(nullptr, 223, nullptr);
}

static void queueStop() {
    const std::string filename = longString("mt_msg_lifetime_stop_source_", 's', ".sv");
    const std::string hier = longString("mt_msg_lifetime_stop_hier_", 'h');
    VL_STOP_MT(filename.c_str(), 124, hier.c_str(), false);
    VL_STOP_MT("", 174, "", false);
    VL_STOP_MT(nullptr, 224, nullptr, false);
}

static void queueFatal() {
    const std::string filename = longString("mt_msg_lifetime_fatal_source_", 'f', ".sv");
    const std::string hier = longString("mt_msg_lifetime_fatal_hier_", 'h');
    const std::string message = longString("mt_msg_lifetime_fatal_message_", 'm');
    VL_FATAL_MT(filename.c_str(), 125, hier.c_str(), message.c_str());
    VL_FATAL_MT("", 175, "", "");
    VL_FATAL_MT(nullptr, 225, nullptr, nullptr);
}

static void churnHeap() {
    for (int i = 0; i < 4096; ++i) {
        const std::string poison = longString("mt_msg_lifetime_poison_", 'x');
        if (poison.empty()) std::abort();
    }
}

static void checkRecords(const std::vector<MessageRecord>& records, int line,
                         const std::string& filename, const std::string& hier,
                         const std::string& message, bool haveMessage) {
    if (records.size() != 3) fail("message count mismatch");
    checkRecord(records[0], line, false, filename, false, hier, !haveMessage, message);
    checkRecord(records[1], line + 50, false, "", false, "", !haveMessage, "");
    checkRecord(records[2], line + 100, true, "", true, "", true, "");
}

int main(int argc, char** argv) {
    if (argc != 2) fail("expected one wrapper mode");
    const std::string mode = argv[1];

    VerilatedContext context;
    Verilated::threadContextp(&context);
    VerilatedEvalMsgQueue evalMsgQ;
    Verilated::mtaskId(1);

    if (mode == "warn") {
        queueWarning();
    } else if (mode == "finish") {
        queueFinish();
    } else if (mode == "stop") {
        queueStop();
    } else if (mode == "fatal") {
        queueFatal();
    } else {
        fail("unknown wrapper mode");
    }
    churnHeap();

    Verilated::endOfThreadMTask(&evalMsgQ);
    Verilated::endOfEval(&evalMsgQ);

    if (mode == "warn") {
        checkRecords(s_warnRecords, 122, longString("mt_msg_lifetime_warn_source_", 'w', ".sv"),
                     longString("mt_msg_lifetime_warn_hier_", 'h'),
                     longString("mt_msg_lifetime_warn_message_", 'm'), true);
    } else if (mode == "finish") {
        checkRecords(s_finishRecords, 123,
                     longString("mt_msg_lifetime_finish_source_", 'f', ".sv"),
                     longString("mt_msg_lifetime_finish_hier_", 'h'), "", false);
    } else if (mode == "stop") {
        checkRecords(s_stopRecords, 124, longString("mt_msg_lifetime_stop_source_", 's', ".sv"),
                     longString("mt_msg_lifetime_stop_hier_", 'h'), "", false);
    } else {
        checkRecords(s_fatalRecords, 125, longString("mt_msg_lifetime_fatal_source_", 'f', ".sv"),
                     longString("mt_msg_lifetime_fatal_hier_", 'h'),
                     longString("mt_msg_lifetime_fatal_message_", 'm'), true);
    }

    std::cout << "MT_MSG_LIFETIME_DONE " << mode << '\n';
    return 0;
}
