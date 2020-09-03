// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2016 by Mandy Xu.
// SPDX-License-Identifier: CC0-1.0

module t
  #(parameter[95:0] P = 1)
   (input clk);

   localparam [32:0] M = 4;

   function [M:0] gen_matrix;
      gen_matrix[0] = 1>> M;
   endfunction

   reg [95: 0] lfsr = 0;
   always @(posedge clk) begin
      lfsr <= (1 >> P);
   end

   wire [95: 0] lfsr_w = 1 >> P;

   localparam [95: 0] lfsr_p = 1 >> P;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
