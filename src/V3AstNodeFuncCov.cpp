// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode implementation for functional coverage nodes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 by Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3AstNodeFuncCov.h"

//######################################################################
// Dump methods

void AstCovergroup::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " " << m_name;
    if (m_isClass) str << " [class]";
}

void AstCovergroup::dumpJson(std::ostream& str) const {
    this->AstNode::dumpJson(str);
    str << ", \"name\": " << VString::quotePercent(name());
    if (m_isClass) str << ", \"isClass\": true";
}

void AstCoverpoint::dump(std::ostream& str) const { this->AstNodeFuncCovItem::dump(str); }

void AstCoverpoint::dumpJson(std::ostream& str) const { this->AstNodeFuncCovItem::dumpJson(str); }

void AstCoverBin::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " " << m_name << " ";
    switch (m_type) {
    case VCoverBinsType::USER: str << "user"; break;
    case VCoverBinsType::ARRAY: str << "array"; break;
    case VCoverBinsType::AUTO: str << "auto"; break;
    case VCoverBinsType::BINS_IGNORE: str << "ignore"; break;
    case VCoverBinsType::BINS_ILLEGAL: str << "illegal"; break;
    case VCoverBinsType::DEFAULT: str << "default"; break;
    case VCoverBinsType::BINS_WILDCARD: str << "wildcard"; break;
    case VCoverBinsType::TRANSITION: str << "transition"; break;
    }
    if (m_isArray) str << "[]";
}

void AstCoverBin::dumpJson(std::ostream& str) const {
    this->AstNode::dumpJson(str);
    str << ", \"name\": " << VString::quotePercent(m_name);
    str << ", \"binsType\": ";
    switch (m_type) {
    case VCoverBinsType::USER: str << "\"user\""; break;
    case VCoverBinsType::ARRAY: str << "\"array\""; break;
    case VCoverBinsType::AUTO: str << "\"auto\""; break;
    case VCoverBinsType::BINS_IGNORE: str << "\"ignore\""; break;
    case VCoverBinsType::BINS_ILLEGAL: str << "\"illegal\""; break;
    case VCoverBinsType::DEFAULT: str << "\"default\""; break;
    case VCoverBinsType::BINS_WILDCARD: str << "\"wildcard\""; break;
    case VCoverBinsType::TRANSITION: str << "\"transition\""; break;
    }
    if (m_isArray) str << ", \"isArray\": true";
}

void AstCoverTransItem::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    switch (m_repType) {
    case VTransRepType::NONE: break;
    case VTransRepType::CONSEC: str << " [*]"; break;
    case VTransRepType::GOTO: str << " [->]"; break;
    case VTransRepType::NONCONS: str << " [=]"; break;
    }
}

void AstCoverTransItem::dumpJson(std::ostream& str) const {
    this->AstNode::dumpJson(str);
    if (m_repType != VTransRepType::NONE) {
        str << ", \"repType\": ";
        switch (m_repType) {
        case VTransRepType::NONE: break;
        case VTransRepType::CONSEC: str << "\"consec\""; break;
        case VTransRepType::GOTO: str << "\"goto\""; break;
        case VTransRepType::NONCONS: str << "\"noncons\""; break;
        }
    }
}

void AstCoverTransSet::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " trans_set";
}

void AstCoverTransSet::dumpJson(std::ostream& str) const { this->AstNode::dumpJson(str); }

void AstCoverCross::dump(std::ostream& str) const { this->AstNodeFuncCovItem::dump(str); }

void AstCoverCross::dumpJson(std::ostream& str) const { this->AstNodeFuncCovItem::dumpJson(str); }

void AstCoverCrossBins::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " " << m_name;
}

void AstCoverCrossBins::dumpJson(std::ostream& str) const {
    this->AstNode::dumpJson(str);
    str << ", \"name\": " << VString::quotePercent(m_name);
}

void AstCoverOption::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " ";
    switch (m_type) {
    case VCoverOptionType::WEIGHT: str << "weight"; break;
    case VCoverOptionType::GOAL: str << "goal"; break;
    case VCoverOptionType::AT_LEAST: str << "at_least"; break;
    case VCoverOptionType::AUTO_BIN_MAX: str << "auto_bin_max"; break;
    case VCoverOptionType::PER_INSTANCE: str << "per_instance"; break;
    case VCoverOptionType::COMMENT: str << "comment"; break;
    }
}

void AstCoverOption::dumpJson(std::ostream& str) const {
    this->AstNode::dumpJson(str);
    str << ", \"optionType\": ";
    switch (m_type) {
    case VCoverOptionType::WEIGHT: str << "\"weight\""; break;
    case VCoverOptionType::GOAL: str << "\"goal\""; break;
    case VCoverOptionType::AT_LEAST: str << "\"at_least\""; break;
    case VCoverOptionType::AUTO_BIN_MAX: str << "\"auto_bin_max\""; break;
    case VCoverOptionType::PER_INSTANCE: str << "\"per_instance\""; break;
    case VCoverOptionType::COMMENT: str << "\"comment\""; break;
    }
}

void AstCoverpointRef::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " " << m_name;
}

void AstCoverpointRef::dumpJson(std::ostream& str) const {
    this->AstNode::dumpJson(str);
    str << ", \"name\": " << VString::quotePercent(m_name);
}

void AstCoverSelectExpr::dump(std::ostream& str) const { this->AstNode::dump(str); }

void AstCoverSelectExpr::dumpJson(std::ostream& str) const { this->AstNode::dumpJson(str); }
