// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Target paths that do not lead to a hookable signal
typedef struct packed {
  logic [7:0] a;
  logic [7:0] b;
} pair_t;

interface simple_if;
  pair_t p;
endinterface

module leaf(input logic [7:0] i, output logic [7:0] o);
  logic [7:0] sig;
  assign sig = i + 8'h01;
  assign o = sig;
endmodule

module wrap(input logic [7:0] i, output logic [7:0] o);
  leaf l(.i(i), .o(o));
endmodule

module producer(simple_if b);
  always_comb b.p = {8'h10, 8'h20};
endmodule

module top_module;
  logic clk = 0;
  int cyc = 0;

  logic [15:0] iv = 16'h2010;
  logic [15:0] ov;
  leaf u[2](.i(iv), .o(ov));

  logic [7:0] wo;
  wrap w(.i(iv[7:0]), .o(wo));

  simple_if bi();
  producer pr(.b(bi));

  logic uq;
  udp_xor ud(uq, iv[0], iv[1]);

  // Aggregates for member and index steps that do not fit the type
  typedef struct {
    logic [7:0] arr[2];
    logic [7:0] b;
  } box_t;
  typedef struct packed {
    logic [3:0] a;
    logic [3:0] b;
  } nib_t;

  box_t       s;
  nib_t       na[2];
  logic [7:0] v;

  for (genvar i = 0; i < 1; ++i) begin : g
    box_t gs;
  end
  logic [7:0] mr[4:7];

  initial begin
    s.arr[0] = 8'h12;
    s.b = 8'h34;
    na[0] = 8'h56;
    v = 8'h78;
    g[0].gs.b = 8'h9a;
    #1 $display("%x %x %x %x %x", s.arr[0], s.b, na[0], v, g[0].gs.b);
  end

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    $display("$[%0d| %04x %02x %02x %0d]", cyc, ov, wo, bi.p.a, uq);
    if (cyc > 2) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule

primitive udp_xor(output q, input a, input b);
  table
    0 0 : 0;
    0 1 : 1;
    1 0 : 1;
    1 1 : 0;
  endtable
endprimitive
