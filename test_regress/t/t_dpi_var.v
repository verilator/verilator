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
   int     fr_a;
   int     fr_b;
   int     fr_chk;
   sub sub (.*);

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d in=%x fr_a=%x b=%x fr_chk=%x\n", $time, cyc, in, fr_a, fr_b, fr_chk);
`endif
      cyc <= cyc + 1;
      in <= {in[30:0], in[31]^in[2]^in[0]};
      if (cyc==0) begin
         // Setup
         in <= 32'hd70a4497;
      end
      else if (cyc<3) begin
      end
      else if (cyc<10) begin
         if (fr_chk != fr_a) $stop;
         if (fr_chk != fr_b) $stop;
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
import "DPI-C" context function void mon_register_b(string name, int isOut);
import "DPI-C" context function void mon_register_done();
import "DPI-C" context function void mon_eval();

module sub (/*AUTOARG*/
   // Outputs
   fr_a, fr_b, fr_chk,
   // Inputs
   in
   );

`systemc_imp_header
  void mon_class_name(const char* namep);
  void mon_register_a(const char* namep, void* sigp, bool isOut);
`verilog

`ifdef ATTRIBUTES
   input int in   /*verilator public_flat_rd*/;
   output int fr_a /*verilator public_flat_rw @(posedge t.monclk)*/;
   output int fr_b /*verilator public_flat_rw @(posedge t.monclk)*/;
`else
   input int in;
   output int fr_a;
   output int fr_b;
`endif
   output int fr_chk;

   always @* fr_chk = in + 1;

   initial begin
      // Test the naming
      $c("mon_class_name(this->name());");
      mon_scope_name("%m");
      // Scheme A - pass pointer directly
      $c("mon_register_a(\"in\", &", in, ", false);");
      $c("mon_register_a(\"fr_a\", &", fr_a, ", true);");
      // Scheme B - use VPIish callbacks to see what signals exist
      mon_register_b("in", 0);
      mon_register_b("fr_b", 1);
      mon_register_done();
   end

endmodule
