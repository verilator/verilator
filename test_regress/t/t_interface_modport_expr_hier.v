// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Test modport expressions with hierarchical module instantiation

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// ============================================================
// Scenario A: Single-level hierarchy + expression modport
// ============================================================

interface if_a;
  logic [7:0] raw_in;
  logic [7:0] raw_out;
  modport mp(input .data_in(raw_in), output .data_out(raw_out));
endinterface

// Leaf module: uses modport expression virtual ports
module a_leaf(if_a.mp port);
  assign port.data_out = port.data_in + 8'h10;
endmodule

// Mid-level module: passes interface down
module a_mid(if_a.mp port);
  a_leaf u_leaf(.port(port));
endmodule

// ============================================================
// Scenario B: 2-level deep hierarchy
// ============================================================

interface if_b;
  logic [15:0] x;
  logic [15:0] y;
  modport mp(input .alpha(x), output .beta(y));
endinterface

module b_leaf(if_b.mp port);
  assign port.beta = port.alpha ^ 16'hFFFF;
endmodule

module b_mid(if_b.mp port);
  b_leaf u_leaf(.port(port));
endmodule

module b_top_wrap(if_b.mp port);
  b_mid u_mid(.port(port));
endmodule

// ============================================================
// Scenario C: Nested interface + expression modport + hierarchy
// ============================================================

interface if_c_inner;
  logic [7:0] val;
endinterface

interface if_c_outer;
  if_c_inner inner();
  modport mp(output .w(inner.val), input .r(inner.val));
endinterface

module c_leaf(if_c_outer.mp port);
  assign port.w = 8'hBE;
  wire [7:0] c_read = port.r;
endmodule

module c_mid(if_c_outer.mp port);
  c_leaf u_leaf(.port(port));
endmodule

// ============================================================
// Scenario D: Multiple instances of same wrapper (no cross-talk)
// ============================================================

interface if_d;
  logic [7:0] din;
  logic [7:0] dout;
  modport mp(input .vi(din), output .vo(dout));
endinterface

module d_leaf(if_d.mp port);
  assign port.vo = port.vi + 8'h01;
endmodule

module d_mid(if_d.mp port);
  d_leaf u_leaf(.port(port));
endmodule

// ============================================================
// Top module
// ============================================================

module top;

  // --- Scenario A ---
  if_a ifa();
  a_mid u_a(.port(ifa));

  // --- Scenario B ---
  if_b ifb();
  b_top_wrap u_b(.port(ifb));

  // --- Scenario C ---
  if_c_outer ifc();
  c_mid u_c(.port(ifc));

  // --- Scenario D ---
  if_d ifd();
  d_mid u_d(.port(ifd));

  initial begin
    // Scenario A: single-level hierarchy
    ifa.raw_in = 8'h20;
    #1;
    `checkh(ifa.raw_out, 8'h30);

    // Scenario B: 2-level deep hierarchy
    ifb.x = 16'h1234;
    #1;
    `checkh(ifb.y, 16'hEDCB);

    // Scenario C: nested interface + hierarchy
    #1;
    `checkh(ifc.inner.val, 8'hBE);
    `checkh(u_c.u_leaf.c_read, 8'hBE);

    // Scenario D: single instance through hierarchy
    ifd.din = 8'h10;
    #1;
    `checkh(ifd.dout, 8'h11);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
