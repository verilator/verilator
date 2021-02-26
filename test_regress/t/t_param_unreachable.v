// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Pierre-Henri Horrein
// SPDX-License-Identifier: CC0-1.0

module t (input clk);

   parameter DEPTH = 1;
   reg [DEPTH-1:0] shiftreg_gen;
   reg [DEPTH-1:0] shiftreg;
   reg my_sr_input = '1;

   // shiftreg_gen is generated: it should not raise any warning or error
   always_ff @(posedge clk) begin
      shiftreg_gen[0] <= my_sr_input;
   end
   if (DEPTH > 1) begin
      always_ff @(posedge clk) begin
         shiftreg_gen[DEPTH-1:1] <= shiftreg_gen[DEPTH-2:0];
      end
   end
   // shiftreg is not generated: it can raise a warning
   always_ff @(posedge clk) begin
      shiftreg[0] <= my_sr_input;
      /* verilator lint_off SELRANGE */
      if (DEPTH > 1) shiftreg[DEPTH-1:1] <= shiftreg[DEPTH-2:0];
      /* verilator lint_on SELRANGE */
   end

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
