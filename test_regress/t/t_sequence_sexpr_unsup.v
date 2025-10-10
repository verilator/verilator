// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   int   a;
   int   b;
   int cyc = 0;
   int res0, res1;

   localparam DELAY = 1;

   always @(posedge clk) begin
      cyc <= cyc + 1;
   end

   // NOTE this grammar hasn't been checked with other simulators,
   // is here just to avoid uncovered code lines in the grammar.
   // NOTE using 'property weak' here as sequence/endsequence not supported
   sequence s_a;
      a;
   endsequence : s_a
   sequence s_var;
      logic l1, l2;
      a;
   endsequence

   sequence s_within;
      a within(b);
   endsequence

   sequence s_and;
      a and b;
   endsequence

   sequence s_or;
      a or b;
   endsequence

   sequence s_throughout;
      a throughout b;
   endsequence

   sequence s_intersect;
      a intersect b;
   endsequence

   sequence s_uni_cycdelay_int;
      ## 1 b;
   endsequence
   sequence s_uni_cycdelay_id;
      ## DELAY b;
   endsequence
   sequence s_uni_cycdelay_pid;
      ## ( DELAY ) b;
   endsequence
   sequence s_uni_cycdelay_range;
      ## [1:2] b;
   endsequence
   sequence s_uni_cycdelay_star;
      ## [*] b;
   endsequence
   sequence s_uni_cycdelay_plus;
      ## [+] b;
   endsequence

   sequence s_cycdelay_int;
      a ## 1 b;
   endsequence
   sequence s_cycdelay_id;
      a ## DELAY b;
   endsequence
   sequence s_cycdelay_pid;
      a ## ( DELAY ) b;
   endsequence
   sequence s_cycdelay_range;
      a ## [1:2] b;
   endsequence
   sequence s_cycdelay_star;
      a ## [*] b;
   endsequence
   sequence s_cycdelay_plus;
      a ## [+] b;
   endsequence

   sequence s_booleanabbrev_brastar_int;
      a [* 1 ];
   endsequence
   sequence s_booleanabbrev_brastar;
      a [*];
   endsequence
   sequence s_booleanabbrev_plus;
      a [+];
   endsequence
   sequence s_booleanabbrev_eq;
      a [= 1];
   endsequence
   sequence s_booleanabbrev_eq_range;
      a [= 1:2];
   endsequence
   sequence s_booleanabbrev_minusgt;
      a [-> 1];
   endsequence
   sequence s_booleanabbrev_minusgt_range;
      a [-> 1:2];
   endsequence

   sequence p_arg_seqence(sequence inseq);
      inseq;
   endsequence

   sequence s_firstmatch_a;
      first_match (a);
   endsequence
   sequence s_firstmatch_ab;
      first_match (a, res0 = 1);
   endsequence
   sequence s_firstmatch_abc;
      first_match (a, res0 = 1, res1 = 2);
   endsequence

   cover sequence (s_a) $display("");
   cover sequence (@(posedge a) disable iff (b) s_a) $display("");
   cover sequence (disable iff (b) s_a) $display("");

   always @(posedge clk) begin
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
