// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   reg [7:0] cyc; initial cyc=0;
   reg 	     set_in_task;

   always @ (posedge clk) begin
      if (cyc == 8'd0) begin
	 cyc <= 8'd1;
	 set_in_task <= 0;
      end
      if (cyc == 8'd1) begin
	 cyc <= 8'h2;
	 ttask;
      end
      if (cyc == 8'd2) begin
	 if (!set_in_task) $stop;
	 cyc <= 8'hf;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

   task ttask;
      begin
	 set_in_task <= 1'b1;
      end
   endtask

endmodule
