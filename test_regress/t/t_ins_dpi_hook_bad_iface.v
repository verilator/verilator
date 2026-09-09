// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Interface signals that cannot be hooked
typedef struct {
  logic [7:0] a;
  logic [7:0] b;
} pair_t;

interface simple_if;
  logic [7:0] data;
  pair_t us;
  real rv;
  int seed;
endinterface

module top_module;
  logic clk = 0;
  int r = 0;
  simple_if bi1 ();
  simple_if bi2 ();
  simple_if bi3 ();
  simple_if bi4 ();

  always #5 clk = ~clk;
  always @(posedge clk) r <= $random(bi4.seed);

  initial begin
    bi1.data = 8'h01;
    bi2.us.a = 8'h02;
    bi3.rv = 1.5;
    #20 $display("%x %x %f %0d", bi1.data, bi2.us.a, bi3.rv, r);
    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
