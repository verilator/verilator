// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2016 by Mandy Xu.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off WIDTH

//bug1088

module t (/*AUTOARG*/
   // Outputs
   err_count,
   // Inputs
   clk, syndromes
   );

   input clk;
   input [7:0] syndromes;
   output reg [1:0]  err_count = 0;

   localparam [95:0] M = 96'h4;
   wire [3:0] syn1 = syndromes[0+:M];
   always @(posedge clk) begin
      err_count <= {1'b0, |syn1};
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
