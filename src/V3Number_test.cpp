// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

// CHEAT!
#define V3NUMBER_ASCII_BINARY
#define _V3ERROR_NO_GLOBAL_ 1
#include "V3Error.cpp"
#include "V3FileLine.cpp"
#include "V3Number.cpp"

#include <config_build.h>
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <algorithm>
#include "V3Number.h"

void test(string lhss, string op, string rhss, string exps) {
    char* l1 = strdup(lhss.c_str());
    char* r1 = strdup(rhss.c_str());
    char* e1 = strdup(exps.c_str());

    V3Number lhnum (new FileLine ("ck",__LINE__), l1);
    V3Number rhnum (new FileLine ("ck",__LINE__), r1);
    V3Number expnum (new FileLine("ck",__LINE__), e1);

    V3Number gotnum (new FileLine("ck",__LINE__), expnum.width());

    if (op=="redOr")	 	gotnum.opRedOr		(lhnum);
    else if (op=="redAnd")	gotnum.opRedAnd		(lhnum);
    else if (op=="redXor")	gotnum.opRedXor		(lhnum);
    else if (op=="redXnor")	gotnum.opRedXnor	(lhnum);
    else if (op=="concat")	gotnum.opConcat		(lhnum,rhnum);
    else if (op=="repl")	gotnum.opRepl		(lhnum,rhnum);
    else if (op=="~")	 	gotnum.opNot		(lhnum);
    else if (op=="!")	 	gotnum.opLogNot		(lhnum);
    else if (op=="negate") 	gotnum.opNegate		(lhnum);
    else if (op=="+")	 	gotnum.opAdd		(lhnum,rhnum);
    else if (op=="-")	 	gotnum.opSub		(lhnum,rhnum);
    else if (op=="*")	 	gotnum.opMul		(lhnum,rhnum);
    else if (op=="/")	 	gotnum.opDiv		(lhnum,rhnum);
    else if (op=="%")	 	gotnum.opModDiv		(lhnum,rhnum);
    else if (op=="&")	 	gotnum.opAnd		(lhnum,rhnum);
    else if (op=="|")	 	gotnum.opOr		(lhnum,rhnum);
    else if (op=="<")	 	gotnum.opLt		(lhnum,rhnum);
    else if (op==">")	 	gotnum.opGt		(lhnum,rhnum);
    else if (op==">>")	 	gotnum.opShiftR		(lhnum,rhnum);
    else if (op=="<<")	 	gotnum.opShiftL		(lhnum,rhnum);
    else if (op=="==")	 	gotnum.opEq		(lhnum,rhnum);
    else if (op=="===")	 	gotnum.opCaseEq		(lhnum,rhnum);
    else if (op=="==?")	 	gotnum.opWildEq		(lhnum,rhnum);
    else if (op=="!=")	 	gotnum.opNeq		(lhnum,rhnum);
    else if (op=="!==")	 	gotnum.opCaseNeq	(lhnum,rhnum);
    else if (op=="!=?")	 	gotnum.opWildNeq	(lhnum,rhnum);
    else if (op=="<=")	 	gotnum.opLte		(lhnum,rhnum);
    else if (op==">=")	 	gotnum.opGte		(lhnum,rhnum);
    else if (op=="&&")	 	gotnum.opLogAnd		(lhnum,rhnum);
    else if (op=="||")	 	gotnum.opLogOr		(lhnum,rhnum);
    else v3fatalSrc("Bad opcode: "<<op);

    UINFO(0,"------- Test:\n"
	  <<"       "<<lhnum<<" "<<op<<endl
	  <<"       "<<rhnum<<endl
	  <<"     = "<<expnum<<endl
	  <<"    =? "<<gotnum<<endl);

    V3Number ok (new FileLine("ck",__LINE__), 1);
    ok.opCaseEq(expnum,gotnum);
    if (ok.toUInt()!=1) {
	v3fatalSrc("%Error:Test FAILED\n");
    }
}

int main() {
    UINFO(0,"Test starting\n");

    test("32'b10","|","32'b10","32'b10");
    test( "2'bx0","|", "2'b10", "2'b10");
    test("32'b0x","|","32'b10","32'b1x");
    test("32'b10","&","32'b11","32'b10");
    test("32'b10","+","32'b10","32'b100");
    test("3'b000","negate","","3'b000");
    test("3'b001","negate","","3'b111");
    test("32'b11","-","32'b001","32'b10");
    test("3'b000","-","3'b111","3'b001");
    test("3'b000","-","3'b000","3'b000");
    test("57'h000000010F0CCE7","*","57'h10","57'h10F0CCE70");
    test("57'h000000010F0CCE7","*","57'h0DE34E7FFFFFFFF","57'h02A9D57EF0F3319");
    test("67'h7FFFFFFFFFFFFFFFF","*","67'h4000000003C8A8D6A","67'h3FFFFFFFFC3757296");
    test("99'h7FFFFFFFFFFFFFFFFFFFFFFFF","*","99'h0000000000000000091338A80","99'h7FFFFFFFFFFFFFFFF6ECC7580");

    cout<<"Test completed\n";
}

//###################################################################
// Local Variables:
// compile-command: "make V3Number_test && ./V3Number_test "
// End:
