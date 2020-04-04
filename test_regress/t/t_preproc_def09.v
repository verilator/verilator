// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`undefineall

// Definitions as speced
// Note there are trailing spaces, which spec doesn't show properly
`define D(x,y) initial $display("start", x , y, "end");
'`D( "msg1" , "msg2" )'
'initial $display("start", "msg1"  , "msg2" , "end");'
'`D( " msg1", )'
'initial $display("start", " msg1" , , "end");'
'`D(, "msg2 ")'
'initial $display("start",  , "msg2 ", "end");'
'`D(,)'
'initial $display("start",  , , "end");'
'`D(  ,  )'
'initial $display("start",  , , "end");'
//`D("msg1") // ILLEGAL: only one argument
//`D()       // ILLEGAL: only one empty argument
//`D(,,)     // ILLEGAL: more actual than formal arguments

// Defaults:
`define MACRO1(a=5,b="B",c) $display(a,,b,,c);
'`MACRO1 ( , 2, 3 )'
'$display(5,,2,,3);'
'`MACRO1 ( 1 , , 3 )'
'$display(1 ,,"B",,3 );'
'`MACRO1 ( , 2, )'
'$display(5,,2,,);'
//`MACRO1 ( 1 )  // ILLEGAL: b and c omitted, no default for c

`define MACRO2(a=5, b, c="C") $display(a,,b,,c);
'`MACRO2 (1, , 3)'
'$display(5,,,,"C");'
'`MACRO2 (, 2, )'
'$display(5,,2,,"C");'
'`MACRO2 (, 2)'
'$display(5,,2,,"C");'

`define MACRO3(a=5, b=0, c="C") $display(a,,b,,c);
'`MACRO3 ( 1 )'
'$display(1 ,,0,,"C");'
'`MACRO3 ( )'
'$display(5,,0,,"C");'
//`MACRO3    // ILLEGAL: parentheses required

`define DTOP(a,b) a + b
'`DTOP( `DTOP(b,1), `DTOP(42,a) )'
'b + 1 + 42 + a'

// Local tests
`define MACROQUOTE(a="==)",b="((((",c=() ) 'a b c'
`MACROQUOTE();
'"==)" "((((" () ';

// Also check our line counting doesn't go bad
`define MACROPAREN(a=(6),
		   b=(eq=al),
		   c) 'a b c'
`MACROPAREN(



	    ,,


	    ZOT)
HERE-`__LINE__ - Line71

//======================================================================
