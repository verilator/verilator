// $Id:$
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t_task (/*AUTOARG*/
   // Outputs
   passed, 
   // Inputs
   clk
   );

   input clk;
   output passed;  reg passed; initial passed = 0;
   reg [7:0] cyc; initial cyc=0;
   reg 	     set_in_task;

   always @ (posedge clk) begin
      if (cyc == 8'd0) begin
	 $write("[%0t] t_task: Starting\n",$time);
	 cyc <= 8'd1;
	 set_in_task <= 0;
      end
      if (cyc == 8'd1) begin
	 cyc <= 8'h2;
	 ttask;
      end
      if (cyc == 8'd2) begin
	 if (!set_in_task) $stop;
	 $write("[%0t] t_task: Passed\n",$time);
	 cyc <= 8'hf;
	 passed <= 1'b1;
      end
   end

   task ttask;
      begin
	 $write("[%0t] t_task: In task\n",$time);
	 set_in_task <= 1'b1;
      end
   endtask

endmodule

// Local Variables:
// compile-command: "./vlint __FILE__"
// End:
