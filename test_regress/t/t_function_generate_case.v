// DESCRIPTION: Verilator: Verify references through generate if/case blocks
//
// When a function is defined inside a generate-case item and called via a
// dotted reference (e.g. blk.f()), the FUNCREF must survive generate
// pruning.  Previously the FUNCREF could point to a function in a pruned
// case item, causing a broken-link internal error.
//
// A case item holding only a generate if is directly nested (IEEE 1800-2023
// 27.5), so its blocks are named 'blk' in the module scope, not under a
// 'genblk' scope.
//
// Alternatives of a generate if/case may share a block name, as only one is
// elaborated. References into the elaborated alternative resolve whichever
// alternative it is, and references in unelaborated alternatives are not
// resolved (IEEE 1800-2023 27.5).
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Hongseok Choi
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module sub #(
    parameter int P = 1
) (
    output int o
);
  // Referenced before the blocks are declared
  assign o = blk.f(P);

  generate
    case (P)
      1, 2:
      if (P == 1) begin : blk
        int w = 1;
        function automatic int f(input int i);
          f = i + 10;
        endfunction
      end
      else begin : blk
        int w = 2;
        function automatic int f(input int i);
          f = i + 20;
        endfunction
      end
      4: begin : blk
        int w = 4;
        function automatic int f(input int i);
          f = i + 40;
        endfunction
      end
      default:
      begin : blk
        int w = 7;
        function automatic int f(input int i);
          f = i + 70;
        endfunction
      end
    endcase
  endgenerate
endmodule

module leaf #(
    parameter int V = 0
) (
    input int cyc
);
  int mem;
  assign mem = cyc + V;
  function automatic int get();
    return mem * 2;
  endfunction
endmodule

module core_a #(
    parameter int D = 0,
    parameter int E = 0
);
  int only_a = 7;
  int s = 1;
  int dv = D;
  int ev = E;
endmodule

module core_b #(
    parameter int D = 0,
    parameter int E = 0
);
  int only_b = 8;
  byte s = 2;
  int dv = D;
  int ev = E;
endmodule

interface bus_if #(
    parameter int W = 1
) (
    input int cyc
);
  logic [W-1:0] d;
  assign d = W'(cyc);
  modport mp(input d);
endinterface

class Holder #(
    parameter int W = 1
);
  virtual bus_if #(.W(W)) vif;
  function new(virtual bus_if #(.W(W)) vif);
    this.vif = vif;
  endfunction
endclass

module mid #(
    parameter int R = 1
) (
    input int cyc
);
  function automatic int bump(input int i);
    return i + 11;
  endfunction

  if (R == 1) begin : g
    leaf #(.V(1)) u_a (.cyc);
    leaf #(.V(5)) u_arr[2] (.cyc);
    core_a u_core ();
    bus_if #(.W(7)) bus (.cyc);
    bus_if #(.W(7)) bus_arr[2] (.cyc);
    if (R == 1) begin : h
      int h1 = 31;
    end
    else begin : h
      int h2 = 32;
    end
    int first_only;
    assign first_only = cyc * 3;
    function automatic int bump(input int i);
      return i + first_only;
    endfunction
  end
  else if (R == 2) begin : g
    leaf #(.V(6)) u_m (.cyc);
    core_b u_core ();
    bus_if #(.W(15)) bus (.cyc);
    bus_if #(.W(15)) bus_arr[2] (.cyc);
  end
  else begin : g
    leaf #(.V(2)) u_b (.cyc);
    core_b u_core ();
    bus_if #(.W(9)) bus (.cyc);
    bus_if #(.W(9)) bus_arr[2] (.cyc);
    if (R == 0) begin : h
      int h0 = 33;
    end
    else begin : h
      int h3 = 34;
    end
    // Calls the module's function, not the earlier alternative's
    int bumped;
    assign bumped = bump(cyc);
  end

  // Applies to whichever alternative is elaborated
  defparam g.u_core.D = 50 + R;

  localparam int BUS_W = R == 1 ? 7 : R == 2 ? 15 : 9;
  virtual bus_if #(.W(BUS_W)) vif;
  virtual bus_if #(.W(BUS_W)).mp vmp;
  virtual bus_if #(.W(BUS_W)) vel;
  Holder #(BUS_W) holder;
  initial begin
    vif = g.bus;
    vmp = g.bus.mp;
    vel = g.bus_arr[1];
    holder = new(g.bus);
  end

  case (R)
    1: begin : c
      leaf #(.V(3)) u_c1 (.cyc);
    end
    2: begin : c
      leaf #(.V(7)) u_c2 (.cyc);
    end
    default:
    begin : c
      leaf #(.V(4)) u_c0 (.cyc);
    end
  endcase

  if (R == 1) begin : g_loc
    function automatic int get();
      return g.u_a.mem + c.u_c1.mem;
    endfunction
  end
  else if (R == 2) begin : g_loc
    function automatic int get();
      return g.u_m.mem + c.u_c2.mem;
    endfunction
  end
  else begin : g_loc
    function automatic int get();
      return g.u_b.mem + c.u_c0.mem;
    endfunction
  end
endmodule

module t;
  int o1;
  int o2;
  int o4;
  int o7;

  sub #(.P(1)) u1 (.o(o1));
  sub #(.P(2)) u2 (.o(o2));
  sub #(.P(4)) u4 (.o(o4));
  sub #(.P(7)) u7 (.o(o7));

  initial begin
    #1;
    `checkd(o1, 11);
    `checkd(o2, 22);
    `checkd(o4, 44);
    `checkd(o7, 77);
    `checkd(u1.blk.w, 1);
    `checkd(u2.blk.w, 2);
    `checkd(u4.blk.w, 4);
    `checkd(u7.blk.w, 7);
  end

  localparam int R1 = 1;
  localparam int R0 = 0;

  int cyc;

  mid #(.R(R1)) u_r1 (.cyc);
  mid #(.R(2)) u_r2 (.cyc);
  mid #(.R(R0)) u_r0 (.cyc);

  defparam u_r1.g.u_core.E = 99;
  defparam u_r0.g.u_core.E = 97;

  Holder #(15) holder_r2;

  if (R1 == 1) begin : g_chk1
    function automatic int get();
      return u_r1.g.u_a.mem;
    endfunction
  end
  else begin : g_chk1
    function automatic int get();
      return u_r1.g.u_b.mem;
    endfunction
  end

  if (R0 == 1) begin : g_chk0
    function automatic int get();
      return u_r0.g.u_a.mem;
    endfunction
  end
  else begin : g_chk0
    function automatic int get();
      return u_r0.g.u_b.mem;
    endfunction
  end

  initial begin
    holder_r2 = new(u_r2.g.bus);
    for (int i = 0; i < 5; ++i) begin
      cyc = i * 7 + 5;
      #1;
      `checkd(u_r1.g.u_a.mem, cyc + 1);
      `checkd(u_r1.g.u_arr[1].mem, cyc + 5);
      `checkd(u_r1.g.first_only, cyc * 3);
      `checkd(u_r1.g.u_a.get(), 2 * cyc + 2);
      `checkd(u_r1.g.u_arr[1].get(), 2 * cyc + 10);
      `checkd(u_r1.g.bump(cyc), cyc * 4);
      `checkd(u_r2.g.u_m.mem, cyc + 6);
      `checkd(u_r1.g.u_core.only_a, 7);
      `checkd(u_r2.g.u_core.only_b, 8);
      `checkd($bits(u_r1.g.u_core.s), 32);
      `checkd($bits(u_r2.g.u_core.s), 8);
      `checkd(u_r1.g.u_core.dv, 51);
      `checkd(u_r2.g.u_core.dv, 52);
      `checkd(u_r0.g.u_core.dv, 50);
      `checkd(u_r1.g.u_core.ev, 99);
      `checkd(u_r2.g.u_core.ev, 0);
      `checkd(u_r0.g.u_core.ev, 97);
      `checkd(u_r1.g.h.h1, 31);
      `checkd(u_r0.g.h.h0, 33);
      `checkd(u_r0.g.u_b.mem, cyc + 2);
      `checkd(u_r0.g.bumped, cyc + 11);
      `checkd(u_r1.c.u_c1.mem, cyc + 3);
      `checkd(u_r2.c.u_c2.mem, cyc + 7);
      `checkd(u_r0.c.u_c0.mem, cyc + 4);
      `checkd(u_r1.g_loc.get(), 2 * cyc + 4);
      `checkd(u_r2.g_loc.get(), 2 * cyc + 13);
      `checkd(u_r0.g_loc.get(), 2 * cyc + 6);
      `checkd(g_chk1.get(), cyc + 1);
      `checkd(g_chk0.get(), cyc + 2);
      `checkd($bits(u_r1.vif.d), 7);
      `checkd(int'(u_r1.vif.d), cyc % (1 << 7));
      `checkd($bits(u_r2.vmp.d), 15);
      `checkd(int'(u_r2.vmp.d), cyc % (1 << 15));
      `checkd($bits(u_r2.vel.d), 15);
      `checkd(int'(u_r2.vel.d), cyc % (1 << 15));
      `checkd($bits(u_r0.holder.vif.d), 9);
      `checkd(int'(u_r0.holder.vif.d), cyc % (1 << 9));
      `checkd($bits(holder_r2.vif.d), 15);
      `checkd(int'(holder_r2.vif.d), cyc % (1 << 15));
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
