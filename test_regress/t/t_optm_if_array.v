// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   dinitout,
   // Inputs
   clk, rstn
   );

   input clk;
   input rstn;
   output [31:0] dinitout;

   wire zero;
   assign zero = 1'd0;

   reg [31:0] dinit [0:1];
   wire [31:0] dinitout = dinit[0] | dinit[1];

   reg rstn_r;  // .pl file checks that this signal gets optimized away
   always @(posedge clk) begin
      rstn_r <= rstn;
   end

   always @(posedge clk) begin
      if ((rstn_r == 0)) begin // Will optimize away
	 dinit[0] <= '0;
      end
      else begin
	 dinit[0] <= {31'd0, zero};
      end
   end

   always @(posedge clk) begin
      if ((rstn_r == 0)) begin // Will optimize away
	 dinit[1] <= 1234;
      end
      else begin
	 dinit[1] <= 1234;
      end
   end

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
