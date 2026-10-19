// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2001-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated coverage item keys internal header
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use by the Verilated library coverage routines.
///
//=============================================================================

#ifndef VERILATOR_VERILATED_COV_KEY_H_
#define VERILATOR_VERILATED_COV_KEY_H_

#include "verilatedos.h"

#include <cctype>
#include <string>

//=============================================================================
// Data used to edit below file, using vlcovgen

#define VLCOVGEN_ITEM(string_parsed_by_vlcovgen)

// clang-format off
VLCOVGEN_ITEM("'name':'column',      'short':'n',  'group':1, 'default':0,    'descr':'Column number for the item.  Used to disambiguate multiple coverage points on the same line number'")
VLCOVGEN_ITEM("'name':'filename',    'short':'f',  'group':1, 'default':None, 'descr':'Filename of the item'")
VLCOVGEN_ITEM("'name':'linescov',    'short':'S',  'group':1, 'default':'',   'descr':'List of comma-separated lines covered'")
VLCOVGEN_ITEM("'name':'per_instance','short':'P',  'group':1, 'default':0,    'descr':'True if every hierarchy is independently counted; otherwise all hierarchies will be combined into a single count'")
VLCOVGEN_ITEM("'name':'thresh',      'short':'s',  'group':1, 'default':None, 'descr':'Number of hits to consider covered (aka at_least)'")
VLCOVGEN_ITEM("'name':'type',        'short':'t',  'group':1, 'default':'',   'descr':'Type of coverage (block, line, fsm, etc)'")
// Bin attributes
VLCOVGEN_ITEM("'name':'bin',         'short':'B',  'group':0, 'default':'',   'descr':'Bin name for covergroup coverage points'")
VLCOVGEN_ITEM("'name':'bin_type',    'short':'Bt', 'group':0, 'default':'',   'descr':'Kind of a covergroup bin that is not coverable: ignore, illegal, or default'")
VLCOVGEN_ITEM("'name':'comment',     'short':'o',  'group':0, 'default':'',   'descr':'Textual description for the item'")
VLCOVGEN_ITEM("'name':'cross',       'short':'C',  'group':0, 'default':0,    'descr':'True for cross coverage points'")
VLCOVGEN_ITEM("'name':'cross_bins',   'short':'Cb', 'group':0, 'default':'',   'descr':'Comma-separated per-dimension bin names for cross coverage points'")
VLCOVGEN_ITEM("'name':'fsm_from',    'short':'Ff', 'group':0, 'default':'',   'descr':'FSM source state name for structured FSM coverage points'")
VLCOVGEN_ITEM("'name':'fsm_tag',     'short':'Fg', 'group':0, 'default':'',   'descr':'FSM point tag such as reset, reset_include, or default'")
VLCOVGEN_ITEM("'name':'fsm_to',      'short':'Ft', 'group':0, 'default':'',   'descr':'FSM destination state name for structured FSM coverage points'")
VLCOVGEN_ITEM("'name':'fsm_var',     'short':'Fv', 'group':0, 'default':'',   'descr':'FSM state variable name for structured FSM coverage points'")
VLCOVGEN_ITEM("'name':'group_weight','short':'Gw', 'group':0, 'default':None, 'descr':'For totaling covergroups, type_option.weight of the covergroup of this item'")
VLCOVGEN_ITEM("'name':'hier',        'short':'h',  'group':0, 'default':'',   'descr':'Hierarchy path name for the item'")
VLCOVGEN_ITEM("'name':'lineno',      'short':'l',  'group':0, 'default':0,    'descr':'Line number for the item'")
VLCOVGEN_ITEM("'name':'weight',      'short':'w',  'group':0, 'default':None, 'descr':'For totaling items, weight of this item'")
// clang-format on

// VLCOVGEN_CIK_AUTO_EDIT_BEGIN
#define VL_CIK_BIN "B"
#define VL_CIK_BIN_TYPE "Bt"
#define VL_CIK_COLUMN "n"
#define VL_CIK_COMMENT "o"
#define VL_CIK_CROSS "C"
#define VL_CIK_CROSS_BINS "Cb"
#define VL_CIK_FILENAME "f"
#define VL_CIK_FSM_FROM "Ff"
#define VL_CIK_FSM_TAG "Fg"
#define VL_CIK_FSM_TO "Ft"
#define VL_CIK_FSM_VAR "Fv"
#define VL_CIK_GROUP_WEIGHT "Gw"
#define VL_CIK_HIER "h"
#define VL_CIK_LINENO "l"
#define VL_CIK_LINESCOV "S"
#define VL_CIK_PER_INSTANCE "P"
#define VL_CIK_THRESH "s"
#define VL_CIK_TYPE "t"
#define VL_CIK_WEIGHT "w"
// VLCOVGEN_CIK_AUTO_EDIT_END

//=============================================================================
// VerilatedCovKey
// Namespace-style static class for \internal use.

class VerilatedCovKey final {
public:
    // The escaping of the keys and values of the records of a coverage file, which the Verilated
    // model writes, and verilator_coverage reads, so defined only here: '%', '"', and characters
    // that do not print, as '%' and two upper-case hex digits, so that each record is a line,
    // whose fields readers can find
    static std::string escape(const std::string& text) VL_PURE {
        std::string result;
        for (const char c : text) {
            const unsigned char u = static_cast<unsigned char>(c);
            if (std::isprint(u) && c != '%' && c != '"') {
                result += c;
            } else {
                result += '%';
                result += "0123456789ABCDEF"[u >> 4];
                result += "0123456789ABCDEF"[u & 0xf];
            }
        }
        return result;
    }
    // A key or value of a record, with the escapes of escape() of the characters that print, as
    // '"' and '%', undone.  Those of characters that do not print stay, so that the text stays a
    // line, as in readers' outputs; as does a '%' that does not begin an escape.
    static std::string unescape(const std::string& text) VL_PURE {
        if (text.find('%') == std::string::npos) return text;  // Speed: nothing escaped
        std::string result;
        for (size_t i = 0; i < text.size(); ++i) {
            const int high = (text[i] == '%' && i + 2 < text.size()) ? hexValue(text[i + 1]) : -1;
            const int low = high < 0 ? -1 : hexValue(text[i + 2]);
            // The character escaped, or -1, as EOF, which does not print
            const int c = low < 0 ? -1 : high * 16 + low;
            if (std::isprint(c)) {
                result += static_cast<char>(c);
                i += 2;
            } else {
                result += text[i];
            }
        }
        return result;
    }
    // Return the short key code for a given a long coverage key
    static std::string shortKey(const std::string& key) VL_PURE {
        // VLCOVGEN_SHORT_AUTO_EDIT_BEGIN
        if (key == "bin") return VL_CIK_BIN;
        if (key == "bin_type") return VL_CIK_BIN_TYPE;
        if (key == "column") return VL_CIK_COLUMN;
        if (key == "comment") return VL_CIK_COMMENT;
        if (key == "cross") return VL_CIK_CROSS;
        if (key == "cross_bins") return VL_CIK_CROSS_BINS;
        if (key == "filename") return VL_CIK_FILENAME;
        if (key == "fsm_from") return VL_CIK_FSM_FROM;
        if (key == "fsm_tag") return VL_CIK_FSM_TAG;
        if (key == "fsm_to") return VL_CIK_FSM_TO;
        if (key == "fsm_var") return VL_CIK_FSM_VAR;
        if (key == "group_weight") return VL_CIK_GROUP_WEIGHT;
        if (key == "hier") return VL_CIK_HIER;
        if (key == "lineno") return VL_CIK_LINENO;
        if (key == "linescov") return VL_CIK_LINESCOV;
        if (key == "per_instance") return VL_CIK_PER_INSTANCE;
        if (key == "thresh") return VL_CIK_THRESH;
        if (key == "type") return VL_CIK_TYPE;
        if (key == "weight") return VL_CIK_WEIGHT;
        // VLCOVGEN_SHORT_AUTO_EDIT_END
        return key;
    }

private:
    // The value of an upper-case hex digit of escape(), or -1 if not one
    static int hexValue(char c) VL_PURE {
        if (c >= '0' && c <= '9') return c - '0';
        if (c >= 'A' && c <= 'F') return c - 'A' + 10;
        return -1;
    }
};

#endif  // guard
