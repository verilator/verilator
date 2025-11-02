// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module t (
    input wire clk,
    input wire [7:0] i,
    input wire a,
    output reg [7:0] o
);

   reg cond = 0;

   always @(posedge clk) begin
     if (cond) o = i;
     cond = a;
     if (cond) o = ~i;
   end

endmodule
