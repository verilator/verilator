// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Command line option parser
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

#ifndef V3OPTION_PARSER_NO_VOPTION_BOOL
#include "V3Global.h"
#include "V3Options.h"
#endif
#include "V3Error.h"
#include "V3OptionParser.h"
#include "V3String.h"

//######################################################################
// V3OptionParser::Impl
struct V3OptionParser::Impl {
    // TYPES

    // Setting for isOnOffAllowed() and isPartialMatchAllowed()
    enum class en : uint8_t {
        NONE,  // "-opt"
        FONOFF,  // "-fopt" and "-fno-opt"
        ONOFF,  // "-opt" and "-no-opt"
        VALUE  // "-opt val"
    };
    // Base class of actual action classes
    template <en MODE, bool ALLOW_PARTIAL_MATCH = false>
    class ActionBase VL_NOT_FINAL : public ActionIfs {
        bool m_undocumented = false;  // This option is not documented
    public:
        virtual bool isValueNeeded() const override final { return MODE == en::VALUE; }
        virtual bool isFOnOffAllowed() const override final { return MODE == en::FONOFF; }
        virtual bool isOnOffAllowed() const override final { return MODE == en::ONOFF; }
        virtual bool isPartialMatchAllowed() const override final { return ALLOW_PARTIAL_MATCH; }
        virtual bool isUndocumented() const override { return m_undocumented; }
        virtual void undocumented() override { m_undocumented = true; }
    };

    // Actual action classes
    template <typename T>
    class ActionSet;  // "-opt" for bool-ish, "-opt val" for int and string
    template <typename BOOL>
    class ActionFOnOff;  // "-fopt" and "-fno-opt" for bool-ish
    template <typename BOOL>
    class ActionOnOff;  // "-opt" and "-no-opt" for bool-ish
    class ActionCbCall;  // Callback without argument for "-opt"
    class ActionCbOnOff;  // Callback for "-opt" and "-no-opt"
    template <class T>
    class ActionCbVal;  // Callback for "-opt val"
    class ActionCbPartialMatch;  // Callback "-O3" for "-O"
    class ActionCbPartialMatchVal;  // Callback "-debugi-V3Options 3" for "-debugi-"

    // MEMBERS
    std::map<const string, std::unique_ptr<ActionIfs>> m_options;  // All actions for option
    bool m_isFinalized{false};  // Becomes after finalize() is called
    VSpellCheck m_spellCheck;  // Suggests closest option when not found
};

//######################################################################
// Action classes in V3OptionParser::Impl

#define V3OPTION_PARSER_DEF_ACT_CLASS(className, type, body, enType) \
    template <> \
    class V3OptionParser::Impl::className<type> final : public ActionBase<enType> { \
        type* const m_valp; /* Pointer to a option variable*/ \
\
    public: \
        explicit className(type* valp) \
            : m_valp(valp) {} \
        virtual void exec(const char* optp, const char* argp) override { body; } \
    }

V3OPTION_PARSER_DEF_ACT_CLASS(ActionSet, bool, *m_valp = true, en::NONE);
#ifndef V3OPTION_PARSER_NO_VOPTION_BOOL
V3OPTION_PARSER_DEF_ACT_CLASS(ActionSet, VOptionBool, m_valp->setTrueOrFalse(true), en::NONE);
#endif
V3OPTION_PARSER_DEF_ACT_CLASS(ActionSet, int, *m_valp = std::atoi(argp), en::VALUE);
V3OPTION_PARSER_DEF_ACT_CLASS(ActionSet, string, *m_valp = argp, en::VALUE);

V3OPTION_PARSER_DEF_ACT_CLASS(ActionFOnOff, bool, *m_valp = !hasPrefixFNo(optp), en::FONOFF);
V3OPTION_PARSER_DEF_ACT_CLASS(ActionOnOff, bool, *m_valp = !hasPrefixNo(optp), en::ONOFF);
#ifndef V3OPTION_PARSER_NO_VOPTION_BOOL
V3OPTION_PARSER_DEF_ACT_CLASS(ActionOnOff, VOptionBool, m_valp->setTrueOrFalse(!hasPrefixNo(optp)),
                              en::ONOFF);
#endif
#undef V3OPTION_PARSER_DEF_ACT_CLASS

#define V3OPTION_PARSER_DEF_ACT_CB_CLASS(className, funcType, body, ...) \
    class V3OptionParser::Impl::className final : public ActionBase<__VA_ARGS__> { \
        std::function<funcType> m_cb; /* Callback function */ \
\
    public: \
        using CbType = std::function<funcType>; \
        explicit className(CbType cb) \
            : m_cb(std::move(cb)) {} \
        virtual void exec(const char* optp, const char* argp) override { body; } \
    }

V3OPTION_PARSER_DEF_ACT_CB_CLASS(ActionCbCall, void(void), m_cb(), en::NONE);
V3OPTION_PARSER_DEF_ACT_CB_CLASS(ActionCbOnOff, void(bool), m_cb(!hasPrefixNo(optp)), en::ONOFF);
template <>
V3OPTION_PARSER_DEF_ACT_CB_CLASS(ActionCbVal<int>, void(int), m_cb(std::atoi(argp)), en::VALUE);
template <>
V3OPTION_PARSER_DEF_ACT_CB_CLASS(ActionCbVal<const char*>, void(const char*), m_cb(argp),
                                 en::VALUE);
V3OPTION_PARSER_DEF_ACT_CB_CLASS(ActionCbPartialMatch, void(const char*), m_cb(optp), en::NONE,
                                 true);
V3OPTION_PARSER_DEF_ACT_CB_CLASS(ActionCbPartialMatchVal, void(const char*, const char*),
                                 m_cb(optp, argp), en::VALUE, true);

#undef V3OPTION_PARSER_DEF_ACT_CB_CLASS

//######################################################################
// Member functions of V3OptionParser

V3OptionParser::ActionIfs* V3OptionParser::find(const char* optp) {
    const auto it = m_pimpl->m_options.find(optp);
    if (it != m_pimpl->m_options.end()) return it->second.get();  // Exact match
    for (auto&& act : m_pimpl->m_options) {
        if (act.second->isFOnOffAllowed()) {  // Find starts with "-fno"
            if (const char* const nop
                = VString::startsWith(optp, "-fno-") ? (optp + strlen("-fno-")) : nullptr) {
                if (act.first.substr(strlen("-f"), std::string::npos)
                    == nop) {  // [-f]opt = [-fno-]opt
                    return act.second.get();
                }
            }
        }
        if (act.second->isOnOffAllowed()) {  // Find starts with "-no"
            if (const char* const nop
                = VString::startsWith(optp, "-no") ? (optp + strlen("-no")) : nullptr) {
                if (act.first == nop || act.first == (std::string{"-"} + nop)) {
                    return act.second.get();
                }
            }
        } else if (act.second->isPartialMatchAllowed()) {
            if (VString::startsWith(optp, act.first)) return act.second.get();
        }
    }
    return nullptr;
}

template <class ACT, class ARG>
V3OptionParser::ActionIfs& V3OptionParser::add(const std::string& opt, ARG arg) {
    UASSERT(!m_pimpl->m_isFinalized, "Cannot add after finalize() is called");
    std::unique_ptr<ACT> act{new ACT{std::move(arg)}};
    UASSERT(opt.size() >= 2, opt << " is too short");
    UASSERT(opt[0] == '-' || opt[0] == '+', opt << " does not start with either '-' or '+'");
    UASSERT(!(opt[0] == '-' && opt[1] == '-'), "Option must have single '-', but " << opt);
    const auto insertedResult = m_pimpl->m_options.emplace(opt, std::move(act));
    UASSERT(insertedResult.second, opt << " is already registered");
    return *insertedResult.first->second;
}

bool V3OptionParser::hasPrefixFNo(const char* strp) {
    UASSERT(strp[0] == '-', strp << " does not start with '-'");
    if (strp[1] == '-') ++strp;
    return VString::startsWith(strp, "-fno");
}

bool V3OptionParser::hasPrefixNo(const char* strp) {
    UASSERT(strp[0] == '-', strp << " does not start with '-'");
    if (strp[1] == '-') ++strp;
    return VString::startsWith(strp, "-no");
}

int V3OptionParser::parse(int idx, int argc, char* argv[]) {
    UASSERT(m_pimpl->m_isFinalized, "finalize() must be called before parse()");
    const char* optp = argv[idx];
    if (optp[0] == '-' && optp[1] == '-') ++optp;
    ActionIfs* const actp = find(optp);
    if (!actp) return 0;
    if (!actp->isValueNeeded()) {
        actp->exec(optp, nullptr);
        return 1;
    } else if (idx + 1 < argc) {
        actp->exec(optp, argv[idx + 1]);
        return 2;
    }
    return 0;
}

string V3OptionParser::getSuggestion(const char* str) const {
    return m_pimpl->m_spellCheck.bestCandidateMsg(str);
}

void V3OptionParser::addSuggestionCandidate(const string& s) {
    m_pimpl->m_spellCheck.pushCandidate(s);
}

void V3OptionParser::finalize() {
    UASSERT(!m_pimpl->m_isFinalized, "finalize() must not be called twice");
    for (auto&& opt : m_pimpl->m_options) {
        if (opt.second->isUndocumented()) continue;
        m_pimpl->m_spellCheck.pushCandidate(opt.first);
        if (opt.second->isFOnOffAllowed()) {
            m_pimpl->m_spellCheck.pushCandidate(
                "-fno-" + opt.first.substr(strlen("-f"), std::string::npos));
        }
        if (opt.second->isOnOffAllowed()) m_pimpl->m_spellCheck.pushCandidate("-no" + opt.first);
    }
    m_pimpl->m_isFinalized = true;
}

V3OptionParser::V3OptionParser()
    : m_pimpl{new Impl{}} {}

V3OptionParser::~V3OptionParser() = default;

//######################################################################
// Member functions of V3OptionParser::AppendHelper

#define V3OPTION_PARSER_DEF_OP(actKind, argType, actType) \
    V3OptionParser::ActionIfs& V3OptionParser::AppendHelper::operator()( \
        const char* optp, actKind, argType arg) const { \
        return m_parser.add<Impl::actType>(optp, arg); \
    }
V3OPTION_PARSER_DEF_OP(Set, bool*, ActionSet<bool>)
#ifndef V3OPTION_PARSER_NO_VOPTION_BOOL
V3OPTION_PARSER_DEF_OP(Set, VOptionBool*, ActionSet<VOptionBool>)
#endif
V3OPTION_PARSER_DEF_OP(Set, int*, ActionSet<int>)
V3OPTION_PARSER_DEF_OP(Set, string*, ActionSet<string>)
V3OPTION_PARSER_DEF_OP(FOnOff, bool*, ActionFOnOff<bool>)
V3OPTION_PARSER_DEF_OP(OnOff, bool*, ActionOnOff<bool>)
#ifndef V3OPTION_PARSER_NO_VOPTION_BOOL
V3OPTION_PARSER_DEF_OP(OnOff, VOptionBool*, ActionOnOff<VOptionBool>)
#endif
V3OPTION_PARSER_DEF_OP(CbCall, Impl::ActionCbCall::CbType, ActionCbCall)
V3OPTION_PARSER_DEF_OP(CbOnOff, Impl::ActionCbOnOff::CbType, ActionCbOnOff)
V3OPTION_PARSER_DEF_OP(CbVal, Impl::ActionCbVal<int>::CbType, ActionCbVal<int>)
V3OPTION_PARSER_DEF_OP(CbVal, Impl::ActionCbVal<const char*>::CbType, ActionCbVal<const char*>)
#undef V3OPTION_PARSER_DEF_OP

V3OptionParser::ActionIfs&
V3OptionParser::AppendHelper::operator()(const char* optp, CbPartialMatch,
                                         Impl::ActionCbPartialMatch::CbType cb) const {
    const size_t prefixLen = std::strlen(optp);
    const auto wrap = [prefixLen, cb](const char* optp) { cb(optp + prefixLen); };
    return m_parser.add<Impl::ActionCbPartialMatch>(optp, std::move(wrap));
}

V3OptionParser::ActionIfs&
V3OptionParser::AppendHelper::operator()(const char* optp, CbPartialMatchVal,
                                         Impl::ActionCbPartialMatchVal::CbType cb) const {
    const size_t prefixLen = std::strlen(optp);
    const auto wrap
        = [prefixLen, cb](const char* optp, const char* argp) { cb(optp + prefixLen, argp); };
    return m_parser.add<Impl::ActionCbPartialMatchVal>(optp, std::move(wrap));
}
