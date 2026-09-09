// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Leaves addressed by an element and a member step, next to a clock member, and a packed
// struct member read through a continuous assignment
module top_module;
  typedef struct packed {
    logic [3:0] a;
    logic [3:0] b;
  } nib_t;
  typedef struct {logic [7:0] arr[2];} box_t;
  typedef struct {
    logic       c;
    logic [7:0] d;
  } clkd_t;
  typedef struct packed {
    logic [7:0] hi;
    logic [7:0] lo;
  } pair_t;

  nib_t       na[2];
  box_t       s;
  clkd_t      cs = '{c: 1'b0, d: 8'h01};
  pair_t      pu = '0;
  logic [7:0] obsHi;
  logic [7:0] obsLo;
  logic [7:0] acc = 0;
  int         cyc = 0;

  assign obsHi = pu.hi;
  assign obsLo = pu.lo;

  always #5 cs.c = ~cs.c;

  always @(posedge cs.c) begin
    cyc <= cyc + 1;
    na[0] <= 8'h12;
    na[1] <= {cyc[3:0], 4'h4};
    s.arr[0] <= 8'h56;
    s.arr[1] <= 8'h70 + cyc[7:0];
    acc <= acc + cs.d;
    pu.hi <= 8'h10 + cyc[7:0];
    pu.lo <= 8'h20;
    $display("$[%0d| na[1]: %x%x s.arr: %02x %02x acc: %02x]", cyc, na[1].a, na[1].b, s.arr[0],
             s.arr[1], acc);
    $display("[%0d] hi=%02x lo=%02x", cyc, obsHi, obsLo);
    if (cyc > 6) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
