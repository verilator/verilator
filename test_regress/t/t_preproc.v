// $Id$
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2004-2007 by Wilson Snyder.

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

// rt.cpan.org bug34429
`define ADD_UP(a,c)          \
wire  tmp_``a = a; \
wire  tmp_``c = tmp_``a + 1; \
assign c = tmp_``c ;

`ADD_UP(d1,o1)   // expansion is OK
`ADD_UP( d2 , o2 )  // expansion is bad

 `define check(mod, width, flopname, gate, path) \
   generate for (i=0; i<(width); i=i+1) begin \
      psl cover {  path.d[i] & ~path.q[i] & !path.cond & (gate)} report `"fondNoRise: mod.flopname`"; \
      psl cover { ~path.d[i] &  path.q[i] & !path.cond & (gate)} report `"fondNoFall: mod.flopname`"; \
   end endgenerate

// parameterized macro with arguments that are macros
 `define MK		m5k.f
 `define MF		`MK .ctl
 `define CK_fr	(`MF.alive & `MF.alive_m1)

   `check(m5kc_fcl, 3, _ctl_mvldx_m1, `CK_fr,	`MF._ctl_mvldx_m1)	// ignorecmt

// macro call with define that has comma
`define REG_H   6
`define REG_L   7
`define _H      regs[`REG_H]
`define _L      regs[`REG_L]
`define _HL     {`_H, `_L}
`define EX_WRITE(ad, da)      begin addr <= (ad); wdata <= (da); wr <= 1; end
`define EX_READ(ad)           begin addr <= (ad); rd <= 1; end

`EX_READ((`_HL + 1)) and `EX_WRITE((`_HL), rdata)
`EX_READ(`_HL + 1)
`EX_WRITE(`_HL, rdata) 

//===========================================================================
// Ifdef

`define EMPTY_TRUE
`ifndef EMPTY_TRUE
  `error "Empty is still true"
`endif
Line_Preproc_Check `__LINE__
