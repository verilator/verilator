// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Command line option parser
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3OPTION_PARSER_H_
#define VERILATOR_V3OPTION_PARSER_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3ThreadSafety.h"

#include <functional>
#include <memory>
#include <string>

// Not to include V3Option.h here so that VlcMain or other executables can use this file easily.
#ifndef V3OPTION_PARSER_NO_VOPTION_BOOL
class VOptionBool;
#endif

// Typical usage would look as below.
// See also V3Options::parseOptsList() in V3Options.cpp for more detailed usage.
//
//    V3OptionParser parser;
//    V3OptionParser::AppendHelper DECL_OPTION{parser};
//    V3OPTION_PARSER_DECL_TAGS;
//
//    DECL_OPPTION("-help", CbCall, []() { showHelp(); });
//    DECL_OPPTION("-some_opt", Set, &m_intMember});
//    parser.finalize();
//    for (int i = 1; i < argc;) {
//        if (int consumed = parser.parse(i, argc, argv)) {
//            i += consumed;
//        } else {  // error
//            std::cerr << parser.getSuggestion(argv[i]) << std::endl;
//        }
//    }
//

//######################################################################
// V3 OptionParser

class V3OptionParser final {
public:
    // TYPES
    class ActionIfs;
    // Functor to register options to V3OptionParser
    class AppendHelper;
    struct Impl;

private:
    // MEMBERS
    const std::unique_ptr<Impl> m_pimpl;

    // METHODS
    ActionIfs* find(const char* optp) VL_MT_DISABLED;
    template <class ACT, class ARG>
    ActionIfs& add(const string& opt, ARG arg) VL_MT_DISABLED;
    // Returns true if strp starts with "-fno"
    static bool hasPrefixFNo(const char* strp) VL_MT_DISABLED;
    // Returns true if strp starts with "-no"
    static bool hasPrefixNo(const char* strp) VL_MT_DISABLED;

public:
    // METHODS
    // Returns how many args are consumed. 0 means not match
    int parse(int idx, int argc, char* argv[]) VL_MT_DISABLED;
    // Find the most similar option
    string getSuggestion(const char* str) const VL_MT_DISABLED;
    void addSuggestionCandidate(const string& s) VL_MT_DISABLED;
    // Call this function after all options are registered.
    void finalize() VL_MT_DISABLED;

    // CONSTRUCTORS
    V3OptionParser() VL_MT_DISABLED;
    ~V3OptionParser() VL_MT_DISABLED;
};

class V3OptionParser::ActionIfs VL_NOT_FINAL {
public:
    virtual ~ActionIfs() = default;
    virtual bool isValueNeeded() const = 0;  // Need val of "-opt val"
    virtual bool isFOnOffAllowed() const = 0;  // true if "-fno-opt" is allowed
    virtual bool isOnOffAllowed() const = 0;  // true if "-no-opt" is allowed
    virtual bool isPartialMatchAllowed() const = 0;  // true if "-Wno-" matches "-Wno-fatal"
    virtual bool isUndocumented() const = 0;  // Will not be suggested in typo
    // Set a value or run callback
    virtual void exec(const char* optp, const char* valp) = 0;
    // Mark this option undocumented. (Exclude this option from suggestion list).
    virtual void undocumented() = 0;
};

// A helper class to register options
class V3OptionParser::AppendHelper final {
public:
    // TYPES
    // Tag to specify which operator() to call
    struct FOnOff {};  // For ActionFOnOff
    struct OnOff {};  // For ActionOnOff
    struct Set {};  // For ActionSet

    struct CbCall {};  // For ActionCbCall
    struct CbFOnOff {};  // For ActionCbFOnOff
    struct CbOnOff {};  // For ActionCbOnOff
    struct CbPartialMatch {};  // For ActionCbPartialMatch
    struct CbPartialMatchVal {};  // For ActionCbPartialMatchVal
    struct CbVal {};  // For ActionCbVal

private:
    // MEMBERS
    V3OptionParser& m_parser;  // The actual option registry

public:
    // METHODS
    ActionIfs& operator()(const char* optp, Set, bool*) const VL_MT_DISABLED;
#ifndef V3OPTION_PARSER_NO_VOPTION_BOOL
    ActionIfs& operator()(const char* optp, Set, VOptionBool*) const VL_MT_DISABLED;
#endif
    ActionIfs& operator()(const char* optp, Set, int*) const VL_MT_DISABLED;
    ActionIfs& operator()(const char* optp, Set, string*) const VL_MT_DISABLED;

    ActionIfs& operator()(const char* optp, FOnOff, bool*) const VL_MT_DISABLED;
    ActionIfs& operator()(const char* optp, OnOff, bool*) const VL_MT_DISABLED;
#ifndef V3OPTION_PARSER_NO_VOPTION_BOOL
    ActionIfs& operator()(const char* optp, OnOff, VOptionBool*) const VL_MT_DISABLED;
#endif

    ActionIfs& operator()(const char* optp, CbCall,
                          std::function<void(void)>) const VL_MT_DISABLED;
    ActionIfs& operator()(const char* optp, CbFOnOff,
                          std::function<void(bool)>) const VL_MT_DISABLED;
    ActionIfs& operator()(const char* optp, CbOnOff,
                          std::function<void(bool)>) const VL_MT_DISABLED;
    ActionIfs& operator()(const char* optp, CbVal, std::function<void(int)>) const VL_MT_DISABLED;
    ActionIfs& operator()(const char* optp, CbVal,
                          std::function<void(const char*)>) const VL_MT_DISABLED;

    ActionIfs& operator()(const char* optp, CbPartialMatch,
                          std::function<void(const char*)>) const VL_MT_DISABLED;
    ActionIfs& operator()(const char* optp, CbPartialMatchVal,
                          std::function<void(const char*, const char*)>) const VL_MT_DISABLED;

    // CONSTRUCTORS
    explicit AppendHelper(V3OptionParser& parser)
        : m_parser(parser) {}
};

#define V3OPTION_PARSER_DECL_TAGS \
    const auto Set VL_ATTR_UNUSED = V3OptionParser::AppendHelper::Set{}; \
    const auto FOnOff VL_ATTR_UNUSED = V3OptionParser::AppendHelper::FOnOff{}; \
    const auto OnOff VL_ATTR_UNUSED = V3OptionParser::AppendHelper::OnOff{}; \
    const auto CbCall VL_ATTR_UNUSED = V3OptionParser::AppendHelper::CbCall{}; \
    const auto CbFOnOff VL_ATTR_UNUSED = V3OptionParser::AppendHelper::CbFOnOff{}; \
    const auto CbOnOff VL_ATTR_UNUSED = V3OptionParser::AppendHelper::CbOnOff{}; \
    const auto CbPartialMatch VL_ATTR_UNUSED = V3OptionParser::AppendHelper::CbPartialMatch{}; \
    const auto CbPartialMatchVal VL_ATTR_UNUSED \
        = V3OptionParser::AppendHelper::CbPartialMatchVal{}; \
    const auto CbVal VL_ATTR_UNUSED = V3OptionParser::AppendHelper::CbVal{};

//######################################################################

#endif  // guard
