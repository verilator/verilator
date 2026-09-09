// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Callbacks that cannot be imported for a target
module top_module;
  logic clk = 0;
  logic [7:0] narrow = 0;
  logic [127:0] wide = 0;
  logic [7:0] v = 0;
  logic [7:0] o = 0;

  function automatic logic [7:0] cb(input logic [7:0] x);
    return x + 8'h01;
  endfunction

  always #5 clk = ~clk;

  always @(posedge clk) begin
    narrow <= narrow + 1;
    wide <= wide + 1;
    v <= cb(v);
    o <= o ^ 8'h55;
  end

  initial begin
    #20 $display("%x %x %x %x", narrow, wide[7:0], v, o);
    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
