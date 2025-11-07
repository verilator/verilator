// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   wire    monclk = ~clk;

   int     in;
   int     in_a;
   int     in_b;
   int     fr_a;
   int     fr_b;
   int     fr_a2;
   int     fr_b2;
   int     fr_chk;
   sub sub (.*);

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d in=%x sub.in_a=%x sub.in_b=%x fr_a=%x fr_b=%x fr_a2=%x fr_b2=%x fr_chk=%x\n",
           $time, cyc, in, sub.in_a, sub.in_b, fr_a, fr_b, fr_a2, fr_b2, fr_chk);
`endif
      cyc <= cyc + 1;
      in <= {in[30:0], in[31]^in[2]^in[0]};
      // The inputs to sub will be updated externally on the neg-edge so these
      // don't matter for the result
      in_a <= in_a + 1;
      in_b <= in_b + 1;
      if (cyc==0) begin
         // Setup
         in <= 32'hd70a4497;
         in_a <= 0;
         in_b <= 0;
      end
      else if (cyc<3) begin
      end
      else if (cyc<10) begin
         if (fr_chk != fr_a) $stop;
         if (fr_chk != fr_b) $stop;
         if (fr_chk != fr_a2) $stop;
         if (fr_chk != fr_b2) $stop;
      end
      else if (cyc==10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end


   always @(posedge t.monclk) begin
      mon_eval();
   end

endmodule

`ifdef ATTRIBUTES
import "DPI-C" context function void mon_scope_name (input string formatted /*verilator sformat*/ );
`else
import "DPI-C" context function void mon_scope_name (input string formatted);
`endif
import "DPI-C" context function void mon_register_b(string name, int isOut, int n, int addend);
import "DPI-C" context function void mon_register_done();
import "DPI-C" context function void mon_eval();

module sub (/*AUTOARG*/
   // Outputs
   fr_a, fr_b, fr_a2, fr_b2, fr_chk,
   // Inputs
   in, in_a, in_b
   );

`systemc_imp_header
  void mon_class_name(const char* namep);
  void mon_register_a(const char* namep, void* sigp, bool isOut, int n, int addend);
`verilog

   /* verilator lint_off ASSIGNIN */
`ifdef ATTRIBUTES // Sensitivity list accepted for backward compatibility but ignored
   input int in   /*verilator public_flat_rd*/;
   input int in_a /*verilator public_flat_rw @(posedge t.monclk)*/;
   input int in_b /*verilator public_flat_rw*/;
   output int fr_a /*verilator public_flat_rw @(posedge t.monclk)*/;
   output int fr_b /*verilator public_flat_rw*/;
`else
   input int in;
   input int in_a;
   input int in_b;
   output int fr_a;
   output int fr_b;
`endif
   output int fr_a2;
   output int fr_b2;
   output int fr_chk;
   /* verilator lint_on ASSIGNIN */

   always @* fr_a2 = in_a + 1;
   always @* fr_b2 = in_b + 1;
   always @* fr_chk = in + 1;

   initial begin
      // Test the naming
      $c("mon_class_name(this->vlNamep);");
      mon_scope_name("%m");
      // Scheme A - pass pointer directly
      $c("mon_register_a(\"in\", &", in, ", false, 0, 1);");
      $c("mon_register_a(\"fr_a\", &", fr_a, ", true, 0, 1);");
      $c("mon_register_a(\"in\", &", in, ", false, 1, 0);");
      $c("mon_register_a(\"in_a\", &", in_a, ", true, 1, 0);");
      // Scheme B - use VPIish callbacks to see what signals exist
      mon_register_b("in", 0, 2, 1);
      mon_register_b("fr_b", 1, 2, 1);
      mon_register_b("in", 0, 3, 0);
      mon_register_b("in_b", 1, 3, 0);
      mon_register_done();
   end

endmodule
