// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2000-2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

//===========================================================================
// Includes
`include "t_preproc_inc2.vh"

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
`MOREMULTILINE
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
`withquote( x , y)  // Simulators disagree here; some substitute "a" others do not

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

/* Define inside comment: `DEEPER and `WITHTICK */
// More commentary: `zap(bug1); `zap("bug2");

//======================================================================
// display passthru

`define ls left_side
`define rs right_side
`define noarg  na
`define thru(x) x
`define thruthru `ls `rs	// Doesn't expand
`define msg(x,y) `"x: `\`"y`\`"`"
   initial begin
      //$display(`msg( \`, \`));  // Illegal
      $display(`msg(pre `thru(thrupre `thru(thrumid) thrupost) post,right side));
      $display(`msg(left side,right side));
      $display(`msg( left side , right side ));
      $display(`msg( `ls , `rs ));
      $display(`msg( `noarg , `rs ));
      $display(`msg( prep ( midp1 `ls midp2 ( outp ) ) , `rs ));
      $display(`msg(`noarg,`noarg`noarg));
      $display(`msg( `thruthru , `thruthru ));   // Results vary between simulators
      $display(`msg(`thru(),));  // Empty
      $display(`msg(`thru(left side),`thru(right side)));
      $display(`msg( `thru( left side ) , `thru( right side ) ));
      $display(`"standalone`");

      // Unspecified when the stringification has multiple lines
`define twoline first \
      second
      $display(`msg(twoline, `twoline));
      //$display(`msg(left side, \ right side \ ));  // Not sure \{space} is legal.
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

//======================================================================
// rt.cpan.org bug34429

`define ADD_UP(a,c)          \
wire  tmp_``a = a; \
wire  tmp_``c = tmp_``a + 1; \
assign c = tmp_``c ;

module add1 ( input wire d1, output wire o1);
 `ADD_UP(d1,o1)   // expansion is OK
endmodule
module add2 ( input wire d2, output wire o2);
 `ADD_UP( d2 , o2 )  // expansion is bad
endmodule

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

//======================================================================
// Quotes are legal in protected blocks.  Grr.
module prot();
`protected
    I!#r#e6<_Q{{E2+]I3<[3s)1@D|'E''i!O?]jD>Jo_![Cl)
    #nj1]p,3^1~,="E@QZB\T)eU\pC#C|7=\$J$##A[@-@{Qk]
`endprotected
endmodule
//"

//======================================================================
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
`EX_WRITE(`_HL, rdata)  more

//======================================================================
// include of parameterized file
`define INCNAME "t_preproc_inc4.vh"
`include `INCNAME
`ifndef T_PREPROC_INC4
 `error "No Inc4"
`endif
`undef T_PREPROC_INC4

`ifdef NOT_DEFINED_INC
 `include NOT_DEFINED_INC
`endif

//======================================================================
// macro call with , in {}

`define xxerror(logfile, msg) $blah(logfile,msg)
`xxerror("ab,cd","e,f");
`xxerror(this.logfile, vec);
`xxerror(this.logfile, vec[1,2,3]);
`xxerror(this.logfile, {blah.name(), " is not foo"});

//======================================================================
// pragma/default net type

`pragma foo = 1
`default_nettype none
`default_nettype uwire

//======================================================================
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
// defines split arguments

`define BEGIN begin
`define END end
`define BEGINEND `BEGIN`END
`define quoteit(x) `"x`"
`BEGIN`END   // 2001 spec doesn't require two tokens, so "beginend" ok
`BEGINEND    // 2001 spec doesn't require two tokens, so "beginend" ok
`quoteit(`BEGIN`END)  // No space "beginend"

//======================================================================
// bug106
`define \esc`def got_escaped
`ifdef \esc`def
  `\esc`def
`endif
Not a \`define

//======================================================================
// misparsed comma in submacro
`define sb bee
`define appease_emacs_paren_matcher (
`define sa(l) x,y)
`define sfoo(q,r) q--r
`sfoo(`sa(el),`sb)  submacro has comma paren

//======================================================================
// bug191
`define bug191(bits) $display("bits %d %d", $bits(foo), bits);
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
// It's unclear if the spec allows this; is text_macro_idenitfier before or after substitution?
`define NODS_DEFINED
`define NODS_INDIRECT(x) x
`ifndef `NODS_INDIRECT(NODS_DEFINED)
   `error "Indirect failed"
`endif
`ifdef `NODS_INDIRECT(NODS_UNDEFINED)
   `error "Indirect2 failed"
`endif
//======================================================================
// Metaprogramming
`define REPEAT_0(d)
`define REPEAT_1(d) d
`define REPEAT_2(d) `REPEAT_1(d)d
`define REPEAT_3(d) `REPEAT_2(d)d
`define REPEAT_4(d) `REPEAT_3(d)d

`define CONCAT(a, b) a``b
`define REPEATC(n, d) `CONCAT(`REPEAT_, n)(d)
`define REPEATT(n, d) `REPEAT_``n(d)

`REPEATC(3, hello3 )
`REPEATT(4, hello4 )
//======================================================================
// Include from stringification
`undef T_PREPROC_INC4
`define NODS_CONC_VH(m) `"m.vh`"
`include `NODS_CONC_VH(t_preproc_inc4)
`ifndef T_PREPROC_INC4 `error_here `endif
//======================================================================
// Defines doing defines
// Note the newline on the end - required to form the end of a define
`define DEFINEIT(d) d \

`define _DEFIF_Z_0 1
`define DEFIF_NZ(d,n) `undef d `ifndef _DEFIF_Z_``n `DEFINEIT(`define d 1) `endif
`DEFIF_NZ(TEMP,1)
`ifndef TEMP  `error "bad" `endif
`DEFIF_NZ(TEMP,0)
`ifdef TEMP  `error "bad0" `endif
Line_Preproc_Check `__LINE__
//======================================================================
// Quoted multiline - track line numbers, and ensure \\n gets propagated
`define MULQUOTE "FOO \
  BAR "
`define MULQUOTE2(mq) `MULQUOTE mq `MULQUOTE
Line_Preproc_Check `__LINE__
`MULQUOTE2("arg_line1 \
  arg_line2")
Line_Preproc_Check `__LINE__
//======================================================================
// bug283

`define A a
`define B b
`define C c
// EXP: abc
`define C5 `A``b```C
`C5
`undef A
`undef B
`undef C

`define XTYPE sonet
`define XJOIN(__arg1, __arg2) __arg1``__arg2
`define XACTION `XJOIN(`XTYPE, _frame)
EXP: sonet_frame
`XACTION
//
`define XFRAME frame
`define XACTION2 `XJOIN(sonet_, `XFRAME)
EXP: sonet_frame
`XACTION2
// This result varies between simulators
`define sonet_frame other_frame
`define XACTION3 `XTYPE``_frame
EXP: sonet_frame
`XACTION3

// The existance of non-existance of a base define can make a difference
`define QA_b zzz
`define Q1 `QA``_b
EXP: module zzz ; endmodule
module `Q1 ; endmodule
module `Q1 ; endmodule

`define QA a
EXP: module a_b ; endmodule
module `Q1 ; endmodule
module `Q1 ; endmodule

//======================================================================
// bug311
integer/*NEED_SPACE*/foo;
//======================================================================
// bug441
module t;
   //-----
   // case provided
   // note this does NOT escape as suggested in the mail
`define LEX_CAT(lexem1, lexem2) lexem1``lexem2
`define LEX_ESC(name) \name  \

   initial begin : `LEX_ESC( `LEX_CAT(a[0],_assignment) )   $write("GOT%%m='%m' EXP='%s'\n", "t.\\`LEX_CAT(a[0],_assignment) ");   end
   //-----
   // SHOULD(simulator-dependant): Backslash doesn't prevent arguments from
   // substituting and the \ staying in the expansion
   // Note space after name is important so when substitute it has ending whitespace
`define ESC_CAT(name,name2) \name``_assignment_``name2 \

   initial begin : `ESC_CAT( a[0],a[1] )   $write("GOT%%m='%m' EXP='%s'\n", "t.\\a[0]_assignment_a[1] ");   end
`undef ESC_CAT
   //-----
`define CAT(a,b) a``b
`define ESC(name) \`CAT(name,suffix)
   // RULE: Ignoring backslash does NOT allow an additional expansion level
   // (Because ESC gets expanded then the \ has it's normal escape meaning)
   initial begin : `ESC(pp)   $write("GOT%%m='%m' EXP='%s'\n", "t.\\`CAT(pp,suffix) ");   end
`undef CAT `undef ESC
   //-----
`define CAT(a,b) a``b
`define ESC(name) \name \

   // Similar to above; \ does not allow expansion after substitution
   initial begin : `ESC( `CAT(ff,bb) )   $write("GOT%%m='%m' EXP='%s'\n", "t.\\`CAT(ff,bb) ");   end
`undef CAT `undef ESC
   //-----
`define ESC(name) \name \

   // MUST: Unknown macro with backslash escape stays as escaped symbol name
   initial begin : `ESC( `zzz )   $write("GOT%%m='%m' EXP='%s'\n", "t.\\`zzz ");   end
`undef ESC
   //-----
`define FOO bar
`define ESC(name) \name \

   // SHOULD(simulator-dependant): Known macro with backslash escape expands
   initial begin : `ESC( `FOO )    $write("GOT%%m='%m' OTHER_EXP='%s'\n OUR_EXP='%s'", "t.bar ","t.\\`FOO ");  end
   // SHOULD(simulator-dependant): Prefix breaks the above
   initial begin : `ESC( xx`FOO )   $write("GOT%%m='%m' EXP='%s'\n", "t.\\xx`FOO ");  end
`undef FOO `undef ESC
   //-----
   // MUST: Unknown macro not under call with backslash escape doesn't expand
`undef UNKNOWN
   initial begin : \`UNKNOWN   $write("GOT%%m='%m' EXP='%s'\n", "t.\\`UNKNOWN ");   end
   //-----
   // MUST: Unknown macro not under call doesn't expand
`define DEF_NO_EXPAND  error_dont_expand
   initial begin : \`DEF_NO_EXPAND   $write("GOT%%m='%m' EXP='%s'\n", "t.\\`DEF_NO_EXPAND ");   end
`undef DEF_NO_EXPAND
   //-----
   // bug441 derivative
   // SHOULD(simulator-dependant): Quotes doesn't prevent arguments from expanding (like backslashes above)
`define STR(name) "foo name baz"
   initial $write("GOT='%s' EXP='%s'\n", `STR(bar), "foo bar baz");
`undef STR
   //-----
   // RULE: Because there are quotes after substituting STR, the `A does NOT expand
`define STR(name) "foo name baz"
`define A(name) boo name hiss
   initial $write("GOT='%s' EXP='%s'\n", `STR(`A(bar)), "foo `A(bar) baz");
`undef A  `undef STR
   //----
   // bug845
`define SLASHED "1//2.3"
   initial $write("Slashed=`%s'\n", `SLASHED);
   //----
   // bug915
`define BUG915(a,b,c) \
       $display("%s%s",a,`"b``c``\n`")
   initial `BUG915("a1",b2,c3);
endmodule

//======================================================================
//bug1225

`define X_ITEM(SUB,UNIT) `X_STRING(SUB``UNIT)
`define X_STRING(A) `"A`"
$display(`X_ITEM(RAM,0));
$display(`X_ITEM(CPU,));

`define EMPTY
`define EMPTYP(foo)
`define SOME some
`define SOMEP(foo) foo

`define XXE_FAMILY XXE_```EMPTY
XXE_FAMILY = `XXE_FAMILY
`define XXE_```EMPTY
`ifdef XXE_
     $display("XXE_ is defined");
`endif

`define XYE_FAMILY XYE_```EMPTYP(foo)
XYE_FAMILY = `XYE_FAMILY
`define XYE_```EMPTYP(foo)
`ifdef XYE_
     $display("XYE_ is defined");
`endif

`define XXS_FAMILY XXS_```SOME
XXS_FAMILY = `XXS_FAMILY
`define XXS_```SOME
`ifdef XXS_some
     $display("XXS_some is defined");
`endif

`define XYS_FAMILY XYS_```SOMEP(foo)
XYS_FAMILY = `XYS_FAMILY
`define XYS_```SOMEP(foo)
`ifdef XYS_foo
     $display("XYS_foo is defined");
`endif

//====

`ifdef NEVER
 `define NXE_FAMILY NXE_```EMPTY
NXE_FAMILY = `NXE_FAMILY
 `define NXE_```EMPTY
 `ifdef NXE_
     $display("NXE_ is defined");
 `endif

 `define NYE_FAMILY NYE_```EMPTYP(foo)
NYE_FAMILY = `NYE_FAMILY
 `define NYE_```EMPTYP(foo)
 `ifdef NYE_
     $display("NYE_ is defined");
 `endif

 `define NXS_FAMILY NXS_```SOME
NXS_FAMILY = `NXS_FAMILY
 `define NXS_```SOME
 `ifdef NXS_some
     $display("NXS_some is defined");
 `endif

 `define NYS_FAMILY NYS_```SOMEP(foo)
NYS_FAMILY = `NYS_FAMILY
 `define NYS_```SOMEP(foo)
 `ifdef NYS_foo
     $display("NYS_foo is defined");
 `endif

 `include `EMPTY

`endif // NEVER

//bug1227
`define INSTANCE(NAME) (.mySig (myInterface.``NAME),
`INSTANCE(pa5)

//======================================================================
// Stringify bug

`define hack(GRP) `dbg_hdl(UVM_LOW, (`"Functional coverage enabled: GRP`"));
`hack(paramgrp)

`define dbg_hdl(LVL, MSG)      $display ("DEBUG : %s [%m]", $sformatf MSG)
`define svfcov_new(GRP) \
   initial do begin `dbg_hdl(UVM_LOW, (`"Functional coverage enabled: GRP`")); end while(0)
`define simple_svfcov_clk(LBL, CLK, RST, ARG) \
  covergroup LBL @(posedge CLK); \
    c: coverpoint ARG iff ((RST) === 1'b1); endgroup \
      LBL u_``LBL; `svfcov_new(u_``LBL)

module pcc2_cfg;
  generate
   `simple_svfcov_clk(a, b, c, d);
  endgenerate
endmodule

//======================================================================
// IEEE mandated predefines
`undefineall  // undefineall should have no effect on these
predef `SV_COV_START 0
predef `SV_COV_STOP 1
predef `SV_COV_RESET 2
predef `SV_COV_CHECK 3
predef `SV_COV_MODULE 10
predef `SV_COV_HIER 11
predef `SV_COV_ASSERTION 20
predef `SV_COV_FSM_STATE 21
predef `SV_COV_STATEMENT 22
predef `SV_COV_TOGGLE 23
predef `SV_COV_OVERFLOW -2
predef `SV_COV_ERROR -1
predef `SV_COV_NOCOV 0
predef `SV_COV_OK 1
predef `SV_COV_PARTIAL 2
//======================================================================
// After `undefineall above, for testing --dump-defines
`define WITH_ARG(a) (a)(a)
