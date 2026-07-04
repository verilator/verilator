// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Mixed-width inside-range bound under an implication (and other single-BOTH
// contexts) must be zero-extended in the emitted SMT.
class Impl;
  rand bit [63:0] x, y;
  rand bit [31:0] g;
  constraint c {
    g inside {[1:10]};
    y == 64'h100;
    y != 0 -> x inside {[y - g : y]};
  }
endclass

class Neg;  // inside under logical-not under implication
  rand bit [63:0] x, y;
  rand bit [31:0] g;
  constraint c {
    g inside {[1:10]};
    y == 64'h100;
    y != 0 -> !(x inside {[y - g : y - 1]});
  }
endclass

class LAnd;  // inside as a logical-and operand (no implication)
  rand bit [63:0] x, y;
  rand bit [31:0] g;
  constraint c {
    g inside {[1:10]};
    y == 64'h100;
    (x inside {[y - g : y]}) && (x[0] == 1'b0);
  }
endclass

class Nest;  // nested implication a -> (b -> inside)
  rand bit [63:0] x, y;
  rand bit [31:0] g;
  rand bit a, b;
  constraint c {
    g inside {[1:10]};
    y == 64'h100;
    a == 1;
    b == 1;
    a -> (b -> x inside {[y - g : y]});
  }
endclass

class CondCtx;  // inside as a ?: condition
  rand bit [63:0] x, y;
  rand bit [31:0] g;
  rand bit s;
  constraint c {
    g inside {[1:10]};
    y == 64'h100;
    (x inside {[y - g : y]}) ? (s == 1'b1) : (s == 1'b0);
  }
endclass

class Ctl;  // all-32-bit control: no extension needed anywhere
  rand bit [31:0] x, y, g;
  constraint c {
    g inside {[1:10]};
    y == 32'h100;
    y != 0 -> x inside {[y - g : y]};
  }
endclass

class DistRange;  // mixed-width dist range bound (kept for constraint lowering)
  rand bit [63:0] x, y;
  rand bit [31:0] g;
  constraint c {
    g inside {[1:10]};
    y == 64'h100;
    x dist {[y - g : y] := 1, 5 := 1};
  }
endclass

module t;
  Impl im;
  Neg ng;
  LAnd la;
  Nest ne;
  CondCtx cx;
  Ctl ct;
  DistRange dr;
  int ok;
  initial begin
    im = new;
    ng = new;
    la = new;
    ne = new;
    cx = new;
    ct = new;
    dr = new;
    for (int i = 0; i < 20; ++i) begin
      ok = im.randomize();
      `checkd(ok, 1);
      if (im.x < (64'h100 - im.g) || im.x > 64'h100) `checkd(0, 1);

      ok = ng.randomize();
      `checkd(ok, 1);
      if (ng.x >= (64'h100 - ng.g) && ng.x <= 64'hFF) `checkd(0, 1);

      ok = la.randomize();
      `checkd(ok, 1);
      if (la.x < (64'h100 - la.g) || la.x > 64'h100 || la.x[0] !== 1'b0) `checkd(0, 1);

      ok = ne.randomize();
      `checkd(ok, 1);
      if (ne.x < (64'h100 - ne.g) || ne.x > 64'h100) `checkd(0, 1);

      ok = cx.randomize();
      `checkd(ok, 1);
      if (cx.s !== ((cx.x >= (64'h100 - cx.g)) && (cx.x <= 64'h100))) `checkd(0, 1);

      ok = ct.randomize();
      `checkd(ok, 1);
      if (ct.x < (32'h100 - ct.g) || ct.x > 32'h100) `checkd(0, 1);

      ok = dr.randomize();
      `checkd(ok, 1);
      if (dr.x != 5 && (dr.x < (64'h100 - dr.g) || dr.x > 64'h100)) `checkd(0, 1);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
