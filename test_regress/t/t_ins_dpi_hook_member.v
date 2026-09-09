// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Unpacked struct targets (one member (um), two members with their own callbacks (u2),
// struct as a whole (us))
module top_module;
  typedef struct {
    logic [7:0]  a;
    logic [15:0] b;
  } pair_t;

  logic  clk = 0;
  pair_t um, u2, us;
  int    cyc = 0;

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc  <= cyc + 1;
    um.a <= cyc[7:0];
    um.b <= 16'h1000 + cyc[15:0];
    u2.a <= cyc[7:0];
    u2.b <= 16'h1000 + cyc[15:0];
    us.a <= cyc[7:0];
    us.b <= 16'h1000 + cyc[15:0];
    $display("um $[%0d| a: %02x b: %04x]", cyc, um.a, um.b);
    $display("u2 $[%0d| a: %02x b: %04x]", cyc, u2.a, u2.b);
    $display("us $[%0d| a: %02x b: %04x]", cyc, us.a, us.b);
    if (cyc > 5) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
