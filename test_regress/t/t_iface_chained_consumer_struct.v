// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Two-level interface chain.  Inner interface has a typedef that
// depends on its parameter.  Mid interface aliases that typedef.
// A module aliases the alias and uses it in a packed struct, then
// passes $bits(struct) to a width-parameterized child.  All widths
// must use the override value, not the template default.

interface inner_if #(
    parameter int N = 1
) ();
  typedef logic [$clog2(N)-1:0] id_t;
endinterface

interface mid_if #(
    parameter int N = 1
) ();
  inner_if #(.N(N)) inner ();
  typedef inner.id_t id_t;
endinterface

module sink #(
    parameter int W = 1
) (
    input logic [W-1:0] dat_i
);
endmodule

module dut #(
    parameter int N = 1
) ();
  mid_if #(.N(N)) m ();
  typedef m.id_t id_t;
  typedef struct packed {
    id_t id;
    logic [7:0] payload;
  } pkt_t;
  pkt_t pkt_var;
  localparam int W = $bits(pkt_t);
  sink #(.W(W)) s (.dat_i(pkt_var));
endmodule

module t;
  // N=8 gives id_t = 3 bits, so pkt_t = 3 + 8 = 11 bits.
  dut #(.N(8)) u ();

  initial begin
    if (u.W !== 11) begin
      $display("%%Error: u.W=%0d expected 11", u.W);
      $stop;
    end
    if ($bits(u.pkt_var) !== 11) begin
      $display("%%Error: $bits(u.pkt_var)=%0d expected 11", $bits(u.pkt_var));
      $stop;
    end
    if ($bits(u.s.dat_i) !== 11) begin
      $display("%%Error: $bits(u.s.dat_i)=%0d expected 11", $bits(u.s.dat_i));
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
