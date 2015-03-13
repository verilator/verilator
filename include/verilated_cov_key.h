// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2001-2015 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
//
// This is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
//=============================================================================
///
/// \file
/// \brief Coverage item keys
///
//=============================================================================

#ifndef _VERILATED_COV_KEY_H_
#define _VERILATED_COV_KEY_H_ 1

#include "verilatedos.h"

#include <string>
using namespace std;

//=============================================================================
// Data used to edit below file, using vlcovgen

#define VLCOVGEN_ITEM(string_parsed_by_vlcovgen)

VLCOVGEN_ITEM("name=>'col0_name',   short=>'C0', group=>1, default=>undef, descr=>'The column title for the header line of this column'")
VLCOVGEN_ITEM("name=>'col1_name',   short=>'C1', group=>1, default=>undef, ")
VLCOVGEN_ITEM("name=>'col2_name',   short=>'C2', group=>1, default=>undef, ")
VLCOVGEN_ITEM("name=>'col3_name',   short=>'C3', group=>1, default=>undef, ")
VLCOVGEN_ITEM("name=>'column',      short=>'n',  group=>1, default=>0,     descr=>'Column number for the item.  Used to disambiguate multiple coverage points on the same line number'")
VLCOVGEN_ITEM("name=>'filename',    short=>'f',  group=>1, default=>undef, descr=>'Filename of the item'")
VLCOVGEN_ITEM("name=>'groupdesc',   short=>'d',  group=>1, default=>'',    descr=>'Description of the covergroup this item belongs to'")
VLCOVGEN_ITEM("name=>'groupname',   short=>'g',  group=>1, default=>'',    descr=>'Group name of the covergroup this item belongs to'")
VLCOVGEN_ITEM("name=>'groupcmt',    short=>'O',  group=>1, default=>'',    ")
VLCOVGEN_ITEM("name=>'per_instance',short=>'P',  group=>1, default=>0,     descr=>'True if every hierarchy is independently counted; otherwise all hierarchies will be combined into a single count'")
VLCOVGEN_ITEM("name=>'row0_name',   short=>'R0', group=>1, default=>undef, descr=>'The row title for the header line of this row'")
VLCOVGEN_ITEM("name=>'row1_name',   short=>'R1', group=>1, default=>undef, ")
VLCOVGEN_ITEM("name=>'row2_name',   short=>'R2', group=>1, default=>undef, ")
VLCOVGEN_ITEM("name=>'row3_name',   short=>'R3', group=>1, default=>undef, ")
VLCOVGEN_ITEM("name=>'table',       short=>'T',  group=>1, default=>undef, descr=>'The name of the table for automatically generated tables'")
VLCOVGEN_ITEM("name=>'thresh',      short=>'s',  group=>1, default=>undef, ")
VLCOVGEN_ITEM("name=>'type',        short=>'t',  group=>1, default=>'',    descr=>'Type of coverage (block, line, fsm, etc)'")
// Bin attributes
VLCOVGEN_ITEM("name=>'col0',        short=>'c0', group=>0, default=>undef, descr=>'The (enumeration) value name for this column in a table cross' ")
VLCOVGEN_ITEM("name=>'col1',        short=>'c1', group=>0, default=>undef, ")
VLCOVGEN_ITEM("name=>'col2',        short=>'c2', group=>0, default=>undef, ")
VLCOVGEN_ITEM("name=>'col3',        short=>'c3', group=>0, default=>undef, ")
VLCOVGEN_ITEM("name=>'comment',     short=>'o',  group=>0, default=>'',    descr=>'Textual description for the item'")
VLCOVGEN_ITEM("name=>'hier',        short=>'h',  group=>0, default=>'',    descr=>'Hierarchy path name for the item'")
VLCOVGEN_ITEM("name=>'limit',       short=>'L',  group=>0, default=>undef, ")
VLCOVGEN_ITEM("name=>'lineno',      short=>'l',  group=>0, default=>0,     descr=>'Line number for the item'")
VLCOVGEN_ITEM("name=>'row0',        short=>'r0', group=>0, default=>undef, descr=>'The (enumeration) value name for this row in a table cross'")
VLCOVGEN_ITEM("name=>'row1',        short=>'r1', group=>0, default=>undef, ")
VLCOVGEN_ITEM("name=>'row2',        short=>'r2', group=>0, default=>undef, ")
VLCOVGEN_ITEM("name=>'row3',        short=>'r3', group=>0, default=>undef, ")
VLCOVGEN_ITEM("name=>'weight',      short=>'w',  group=>0, default=>undef, descr=>'For totaling items, weight of this item'")

//=============================================================================
//  VerilatedCovKey
///  Verilator coverage global class
////
/// Global class with methods affecting all coverage data.

// VLCOVGEN_CIK_AUTO_EDIT_BEGIN
#define VL_CIK_COL0 "c0"
#define VL_CIK_COL0_NAME "C0"
#define VL_CIK_COL1 "c1"
#define VL_CIK_COL1_NAME "C1"
#define VL_CIK_COL2 "c2"
#define VL_CIK_COL2_NAME "C2"
#define VL_CIK_COL3 "c3"
#define VL_CIK_COL3_NAME "C3"
#define VL_CIK_COLUMN "n"
#define VL_CIK_COMMENT "o"
#define VL_CIK_FILENAME "f"
#define VL_CIK_GROUPCMT "O"
#define VL_CIK_GROUPDESC "d"
#define VL_CIK_GROUPNAME "g"
#define VL_CIK_HIER "h"
#define VL_CIK_LIMIT "L"
#define VL_CIK_LINENO "l"
#define VL_CIK_PER_INSTANCE "P"
#define VL_CIK_ROW0 "r0"
#define VL_CIK_ROW0_NAME "R0"
#define VL_CIK_ROW1 "r1"
#define VL_CIK_ROW1_NAME "R1"
#define VL_CIK_ROW2 "r2"
#define VL_CIK_ROW2_NAME "R2"
#define VL_CIK_ROW3 "r3"
#define VL_CIK_ROW3_NAME "R3"
#define VL_CIK_TABLE "T"
#define VL_CIK_THRESH "s"
#define VL_CIK_TYPE "t"
#define VL_CIK_WEIGHT "w"
// VLCOVGEN_CIK_AUTO_EDIT_END

class VerilatedCovKey {
public:
    static string shortKey(const string& key) {
	// VLCOVGEN_SHORT_AUTO_EDIT_BEGIN
	if (key == "col0") return VL_CIK_COL0;
	if (key == "col0_name") return VL_CIK_COL0_NAME;
	if (key == "col1") return VL_CIK_COL1;
	if (key == "col1_name") return VL_CIK_COL1_NAME;
	if (key == "col2") return VL_CIK_COL2;
	if (key == "col2_name") return VL_CIK_COL2_NAME;
	if (key == "col3") return VL_CIK_COL3;
	if (key == "col3_name") return VL_CIK_COL3_NAME;
	if (key == "column") return VL_CIK_COLUMN;
	if (key == "comment") return VL_CIK_COMMENT;
	if (key == "filename") return VL_CIK_FILENAME;
	if (key == "groupcmt") return VL_CIK_GROUPCMT;
	if (key == "groupdesc") return VL_CIK_GROUPDESC;
	if (key == "groupname") return VL_CIK_GROUPNAME;
	if (key == "hier") return VL_CIK_HIER;
	if (key == "limit") return VL_CIK_LIMIT;
	if (key == "lineno") return VL_CIK_LINENO;
	if (key == "per_instance") return VL_CIK_PER_INSTANCE;
	if (key == "row0") return VL_CIK_ROW0;
	if (key == "row0_name") return VL_CIK_ROW0_NAME;
	if (key == "row1") return VL_CIK_ROW1;
	if (key == "row1_name") return VL_CIK_ROW1_NAME;
	if (key == "row2") return VL_CIK_ROW2;
	if (key == "row2_name") return VL_CIK_ROW2_NAME;
	if (key == "row3") return VL_CIK_ROW3;
	if (key == "row3_name") return VL_CIK_ROW3_NAME;
	if (key == "table") return VL_CIK_TABLE;
	if (key == "thresh") return VL_CIK_THRESH;
	if (key == "type") return VL_CIK_TYPE;
	if (key == "weight") return VL_CIK_WEIGHT;
	// VLCOVGEN_SHORT_AUTO_EDIT_END
	return key;
    }
};

#endif // guard
