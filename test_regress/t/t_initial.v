// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   reg 	 _ranit;

   `include "t_initial_inc.vh"

   // surefire lint_off STMINI
   initial assign user_loaded_value = 1;

   initial _ranit = 0;

   always @ (posedge clk) begin
      if (!_ranit) begin
	 _ranit <= 1;

	 // Test $time
	 // surefire lint_off CWECBB
	 if ($time<20) $write("time<20\n");
	 // surefire lint_on  CWECBB

	 // Test $write
	 $write ("[%0t] %m: User loaded ", $time);
	 $display ("%b", user_loaded_value);
	 if (user_loaded_value!=1) $stop;

	 // Test $c
`ifdef VERILATOR
	 $c ("VL_PRINTF(\"Hi From C++\\n\");");
`endif
	 user_loaded_value <= 2;

	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
