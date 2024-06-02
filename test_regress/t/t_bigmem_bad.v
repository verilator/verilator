// This test shall generate a warning, but not an internal error.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Zhanglei Wang.
// SPDX-License-Identifier: CC0-1.0
module t_bigmem(
   input wire clk,
   input wire [27:0] addr,
   input wire [255:0] data,
   input wire wen
);
   reg [(1<<28)-1:0][255:0] mem;
   always @(posedge clk) begin
      if (wen) mem[addr] <= data;
   end
endmodule
