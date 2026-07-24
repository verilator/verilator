// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Multi-instance: shared classes dedup shadow storage per-instance.

// Parameterized interface: reconstructed signals.
interface iface_t #(parameter W = 8) (input logic [W-1:0] din);
  logic [W-1:0] a;
  logic [W-1:0] b;
  assign a = din + 8'h11;
  assign b = a ^ 8'h5a;
endinterface

// Non-inlined module shared as one C++ class.
module sub (input logic clk, input logic [7:0] din, output logic [7:0] dout);
  /*verilator no_inline_module*/
  logic [7:0] s1;
  logic [7:0] s2;
  assign s1 = din + 8'h07;
  assign s2 = s1 + (din << 1);
  assign dout = s2;
  logic [7:0] wo;
  always_ff @(posedge clk) wo <= din + 8'h11;
endmodule

module t (
  input logic clk,
  input logic [7:0] base,
  output logic [7:0] obs
);

  iface_t #(.W(8)) if0 (.din(base));
  iface_t #(.W(8)) if1 (.din(base + 8'h20));

  logic [7:0] out0;
  logic [7:0] out1;
  sub u0 (.clk(clk), .din(base),         .dout(out0));
  sub u1 (.clk(clk), .din(base + 8'h30), .dout(out1));

  logic [7:0] acc;
  always_ff @(posedge clk) begin
    acc <= acc + if0.b + if1.b + out0 + out1;
  end
  assign obs = acc;

endmodule
