// DESCRIPTION: Verilator: All-ones fields in wide concatenation temporaries
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  int cyc = 0;
  logic [63:0] value = 64'h123456789abcdef0;
  logic [64:0] entry;
  logic [129:0] stack = 0;
  logic [63:0] low = 0, high = 0;
  logic lowv = 0, highv = 0;
  always_comb entry = {1'b1, value[0] ? value + 64'd2 : {value[63:2], 2'b10} + 64'd4};
  always @(posedge clk) begin
    `checkh(stack[63:0], low);
    `checkh(stack[64], lowv);
    `checkh(stack[128:65], high);
    `checkh(stack[129], highv);
    if (value[1]) begin
      stack <= {stack[64:0], entry};
      high <= low;
      highv <= lowv;
      low <= value[0] ? value + 64'd2 : {value[63:2], 2'b10} + 64'd4;
      lowv <= 1;
    end
    else begin
      stack <= {entry, stack[129:65]};
      low <= high;
      lowv <= highv;
      high <= value[0] ? value + 64'd2 : {value[63:2], 2'b10} + 64'd4;
      highv <= 1;
    end
    value <= (value << 1) ^ (value >> 3) ^ 64'h1020304050607080;
    cyc <= cyc + 1;
    if (cyc == 80) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
