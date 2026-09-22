// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Multi-instance and cross-scope --vpi-lazy cases.
interface iface_t;
  logic [6:0] val;
  logic [6:0] derived;
  assign derived = val + 7'h1;
endinterface

// Port-alias helper target.
module sub (
  input  logic [6:0] din,
  output logic [6:0] dout
);
  wire [6:0] din_copy;
  assign din_copy = din;
  assign dout = din_copy ^ 7'h0f;
endmodule

// Different per-instance expressions prevent sharing.
interface iface2_t;
  logic [6:0] a;
  logic [6:0] b;
endinterface

// Non-inlined module shared as one C++ class.
module child (
  input logic clk,
  input logic [7:0] din
);
  /*verilator no_inline_module*/
  logic [7:0] cy;
  assign cy = din ^ 8'hA5;
  logic [7:0] cflop;
  always_ff @(posedge clk) cflop <= din ^ 8'h5a;
endmodule

module parent (
  input logic clk,
  input logic [7:0] din
);
  /*verilator no_inline_module*/
  child uc (.clk(clk), .din(din));
  logic [7:0] py;
  assign py = uc.cy + 8'h03;
  // A cross-scope boundary alias needs local storage.
  logic [7:0] xali;
  assign xali = uc.cflop;
endmodule

module t (
  input logic clk,
  input logic rst,
  input logic [7:0] din0,
  input logic [7:0] din1,
  output logic [6:0] observe,
  output logic [6:0] observe2,
  output logic [7:0] obs_xscope
);

  // multiinst
  logic [6:0] ctr;

  iface_t if_a();
  iface_t if_b();
  iface_t if_c();

  assign if_a.val = ctr + 7'h1;
  assign if_b.val = ctr ^ 7'h2a;
  assign if_c.val = 7'h55;

  logic [6:0] d0;
  logic [6:0] d1;
  sub u0(.din(ctr & 7'h3c), .dout(d0));
  sub u1(.din(ctr | 7'h03), .dout(d1));

  always_ff @(posedge clk) begin
    if (rst) begin
      ctr <= 7'h0;
      observe <= 7'h0;
    end else begin
      ctr <= ctr + 7'h3;
      observe <= if_a.derived ^ if_b.derived ^ if_c.derived ^ d0 ^ d1;
    end
  end

  // multiinst2
  logic [6:0] ctr2;

  iface2_t if0();
  iface2_t if1();

  assign if0.a = ctr2;
  assign if1.a = ctr2 + 7'h1;
  assign if0.b = ~if0.a;
  assign if1.b = if1.a ^ 7'h55;

  always_ff @(posedge clk) begin
    if (rst) begin
      ctr2 <= 7'h0;
      observe2 <= 7'h0;
    end else begin
      ctr2 <= ctr2 + 7'h3;
      observe2 <= if0.b ^ if1.b;
    end
  end

  // xscope
  parent p0 (.clk(clk), .din(din0));
  parent p1 (.clk(clk), .din(din1));

  logic [7:0] acc_xscope;
  always_ff @(posedge clk) begin
    acc_xscope <= acc_xscope + p0.py + p1.py;
  end
  assign obs_xscope = acc_xscope;

endmodule
