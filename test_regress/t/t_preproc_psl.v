// DESCRIPTION: Verilator: Verilog Test module
//
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

// verilator metacomment preserved
/**/
/*verilator metacomment also_preserved*/

Hello in t_preproc_psl.v
   // Psl capitalized not relevant
   // Double commented ignored // psl not ok
   // You can't have multiple statements on one // psl line.
   // Inline /*cmt*/ comments not allowed inside psl comments

   // psl default clock = (posedge clk);
   // psl fails1: cover {cyc==10};
   // psl assert always cyc!=10;
   // psl assert always cyc==3 -> mask==8'h2;
   // psl failsx: cover {cyc==3 && mask==8'h1};
   /* psl fails2:
        cover {
	    cyc==3 && mask==8'h9};
        // Ignore this comment-in-between-statements  (however not legal inside a statement)
	fails3: always assert {
	    cyc==3 && mask==8'h10 };
    */
 `__LINE__

   // Note the PSL statement can be on a unique line
   // There can also be multiple "psl" keywords per line.
   /*
   psl
      fails_ml:
        assert always
  	    cyc==3 -> mask==8'h21;
    psl
      fails_mlalso:  assert always cyc==3 -> mask==8'h21;
    */
 `__LINE__

   // psl assert never (cyc==1 && reset_l);

   // psl fails3: assert always
   //	    cyc==3 -> mask==8'h21;
   //	syntax_error, not_part_of_above_stmt;

// We need to count { and ( when looking for ; that terminate a PSL expression
   // psl assert always
   //       {[*]; cyc==3;
   //        cyc==4; cyc==6};
   //	syntax_error, not_part_of_above_stmt;

// However /**/ pairs can't be split as above.

`ifdef NEVER
   // psl ifdefs have precedence;
`endif

// Macros are expanded...
`define define_sig cyc
   // psl assert always `define_sig!=10;

`ifdef verilator
  `psl
psl assert always sig!=90;
  `verilog
`endif

// Did we end up right?
`__LINE__
