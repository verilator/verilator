// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc=0;

   wire    monclk = ~clk;

   int 	   in;
   int 	   fr_a;
   int 	   fr_b;
   int 	   fr_chk;
   sub sub (.*);

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d in=%x fr_a=%x b=%x fr_chk=%x\n",$time, cyc, in, fr_a, fr_b, fr_chk);
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

endmodule

import "DPI-C" context function void mon_scope_name (input string formatted /*verilator sformat*/ );
import "DPI-C" context function void mon_register_b(string name, int isOut);
import "DPI-C" context function void mon_register_done();

module sub (/*AUTOARG*/
   // Outputs
   fr_a, fr_b, fr_chk,
   // Inputs
   in
   );

`systemc_imp_header
  void mon_class_name(const char* namep);
  void mon_register_a(const char* namep, void* sigp, bool isOut);
  bool mon_eval();
`verilog

   input int in   /*verilator public_flat*/;
   output int fr_a /*verilator public_flat*/;
   output int fr_b /*verilator public_flat*/;
   output int fr_chk;

   reg [3:0]  onearray [1:2] /*verilator public_flat*/;
   reg [3:0]  twoarray [1:2][3:4] /*verilator public_flat*/;

   always @* fr_chk = in + 1;

   initial begin
      // Test the naming
      $c("mon_class_name(name());");
      mon_scope_name("%m");
      // Scheme A - pass pointer directly
      $c("mon_register_a(\"in\",&",in,",false);");
      $c("mon_register_a(\"fr_a\",&",fr_a,",true);");
      // Scheme B - use VPIish callbacks to see what signals exist
      mon_register_b("in", 0);
      mon_register_b("fr_b", 1);
      mon_register_done();
   end

   always @(posedge t.monclk) begin
      // Hack - Write all outputs, so the data will get scheduled to propagate out of this module
      // FUTURE Long term, we should detect a public signal has been written
      // with a new value, and create an event that flips monclk automatically
      if ($c1("mon_eval()")) begin
	 // This code doesn't execute, just is here so verilator schedules the code.
	 fr_a = 0;
	 fr_b = 0;
      end
   end

endmodule
