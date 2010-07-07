// DESCRIPTION: Verilator: Verilog Test module
//
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

`define FOOBAR  foo /*this */ bar   /* this too */
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
`foo(bar)  more

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

//======================================================================
// bug84

`define ARGPAR(a,  // Hello, comments MIGHT not be legal
  /*more,,)cmts*/ b  // But newlines ARE legal... who speced THAT?
  ) (a,b)
`ARGPAR(p,q)
`ARGPAR( //Here
	      x,
  y   //Too
  )
Line_Preproc_Check `__LINE__

//======================================================================
// misparsed comma in submacro
`define sb bee
`define appease_emacs_paren_matcher (
`define sa(l) x,y)
`define sfoo(q,r) q--r
`sfoo(`sa(el),`sb)  submacro has comma paren

//======================================================================
// bug191
`define bug191(bits) $display("bits %d %d", $bits(foo), `bits);
`bug191(10)

//======================================================================
// 1800-2009
`define UDALL
`ifndef PREDEF_COMMAND_LINE `error "Test setup error, PREDEF_COMMAND_LINE pre-missing" `endif
`undefineall
`ifdef UDALL `error "undefineall failed" `endif
`ifndef PREDEF_COMMAND_LINE `error "Deleted too much, no PREDEF_COMMAND_LINE" `endif

//======================================================================
// bug202
`define FC_INV3(out, in)					\
  `ifdef DC							\
     cell \inv_``out <$typeof(out)> (.a(<in>), .o(<out>));	\
      /* multi-line comment					\
	 multi-line comment */					\
  `else								\
    `ifdef MACRO_ATTRIBUTE					\
      (* macro_attribute = `"INV (out``,in``)`" *)		\
    `endif							\
     assign out = ~in ;						\
  `endif

`FC_INV3(a3,b3)

`define /* multi	\
	 line1*/	\
 bug202( i /*multi	\
	   line2*/	\
     )			\
   /* multi		\
      line 3*/		\
   def i		\

`bug202(foo)

//======================================================================

`define CMT1 // verilator NOT IN DEFINE
`define CMT2 /* verilator PART OF DEFINE */
`define CMT3 /* verilator NOT PART
	        OF DEFINE */
`define CMT4 /* verilator PART \
	        OF DEFINE */
`define CMT5 // CMT NOT \
  also in  // BUT TEXT IS \
  also3  // CMT NOT

1 `CMT1 (nodef)
2 `CMT2 (hasdef)
3 `CMT3 (nodef)
4 `CMT4 (nodef)
5 `CMT5 (nodef)
`define NL HAS a NEW \
LINE
`NL

//======================================================================

`define msg_fatal(log, msg)  \
   do \
      /* synopsys translate_off */ \
`ifdef NEVER \
  `error "WTF" \
`else \
      if (start(`__FILE__, `__LINE__)) begin \
`endif \
	 message(msg); \
      end \
      /* synopsys translate_on */ \
   while(0)

`define msg_scen_(cl)   cl``_scen
`define MSG_MACRO_TO_STRING(x) `"x`"

EXP: clxx_scen
`msg_scen_(clxx)
EXP: clxx_scen
`MSG_MACRO_TO_STRING(`msg_scen_(clxx))
`define mf(clx) `msg_fatal(this.log, {"Blah-", `MSG_MACRO_TO_STRING(`msg_scen_(clx)), " end"});
EXP: do if (start("verilog/inc1.v", 25)) begin  message({"Blah-", "clx_scen", " end"}); end  while(0);
`mf(clx)

//======================================================================

`define makedefine(name) \
   `define def_``name   This is name \
   `define def_``name``_2 This is name``_2 \

`makedefine(fooed)
`ifndef def_fooed  `error "No def_fooed" `endif
//`ifndef def_fooed_2  `error "No def_fooed_2" `endif
EXP: This is fooed
`def_fooed
EXP: This is fooed_2
`def_fooed_2

//======================================================================
`define NOPARAM() np
`NOPARAM()
`NOPARAM( )
//======================================================================
