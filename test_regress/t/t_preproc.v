// $Id$
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2004-2006 by Wilson Snyder.

//===========================================================================
// Includes
`include "t_preproc_inc2.v"

//===========================================================================
// Comments

/* verilator pass_thru comment */

// verilator pass_thru_comment2

//===========================================================================
// Defines

`define DEF_A3
`define DEF_A1
// DEF_A0 set by command line
   wire [3:0] q = {
		   `ifdef DEF_A3 1'b1 `else 1'b0 `endif ,
		   `ifdef DEF_A2 1'b1 `else 1'b0 `endif ,
		   `ifdef DEF_A1 1'b1 `else 1'b0 `endif ,
		   `ifdef DEF_A0 1'b1 `else 1'b0 `endif
		   };

text.

`define FOOBAR  foo /*but not */ bar   /* or this either */
`define FOOBAR2  foobar2 // but not
`FOOBAR
`FOOBAR2

`define MULTILINE first part \
  		second part \
  		third part

`define MOREMULTILINE {\
		       a,\
		       b,\
		       c}

/*******COMMENT*****/
`MULTILINE
Line_Preproc_Check `__LINE__

//===========================================================================

`define syn_negedge_reset_l or negedge reset_l

`define DEEP deep
`define DEEPER `DEEP `DEEP
`DEEPER

`define nosubst NOT_SUBSTITUTED
`define WITHTICK "`nosubst"
"Inside: `nosubst"
`WITHTICK		  

`define withparam(a, b) a b LLZZ a b
`withparam(x,y)
`withparam(`withparam(p,q),`withparam ( r , s ))

`withparam(firstline
	,
	comma","line)

`define withquote(a, bar) a bar LLZZ "a" bar
`withquote( x , y)

`define noparam (a,b)
`noparam(a,b)

`define msg(x,y) `"x: `\`"y`\`"`"
$display(`msg(left side, right side))

`define foo(f) f``_suffix
`foo(bar)  

`define zap(which)   \
   	$c("Zap(\"",which,"\");");
`zap(bug1);
`zap("bug2");

//===========================================================================
// Ifdef

`define EMPTY_TRUE
`ifndef EMPTY_TRUE
  `error "Empty is still true"
`endif
Line_Preproc_Check `__LINE__
