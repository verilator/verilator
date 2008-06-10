// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t_initial(/*AUTOARG*/
   // Outputs
   passed,
   // Inputs
   clk
   );
   input clk;
   output passed;  reg passed; initial passed = 0;
   reg 	 _ranit;

   `include "t_initial_inc.v"

   // surefire lint_off STMINI
   initial assign user_loaded_value = 1;

   initial _ranit = 0;

   always @ (posedge clk) begin
      if (!_ranit) begin
	 _ranit <= 1;
	 $write("[%0t] t_initial: Running\n",$time);

	 // Test $time
	 // surefire lint_off CWECBB
	 if ($time<20) $write("time<20\n");
	 // surefire lint_on  CWECBB

	 // Test $write
	 $write ("[%0t] %m: User loaded ", $time);
	 $display ("%b", user_loaded_value);
	 if (user_loaded_value!=1) $stop;

	 // Test $c
`ifdef verilator
	 $c ("cout<<\"Hi From C++\"<<endl;");
`endif
	 user_loaded_value <= 2;

	 $write("[%0t] t_initial: Passed\n",$time);
	 passed <= 1'b1;
      end
   end

endmodule
