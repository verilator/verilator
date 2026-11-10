// DESCRIPTION: Verilator: Accesses through virtual interfaces are seen by the analyses, so
// processes reading and writing members through them are ordered and evaluated again as needed
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface cbus;
  // verilator lint_off UNOPTFLAT
  logic [7:0] x;  // In a loop below
  // verilator lint_on UNOPTFLAT
endinterface

interface bus;
  logic [7:0] y;
endinterface

interface pbus;
  logic [7:0] y;
endinterface

interface wbus;
  int x1, x2, x3;
endinterface

module t;
  bit clk;
  int cyc;
  always #5 clk = ~clk;

  // Combinational logic writing through one virtual interface and reading through another,
  // which may point to the same instance: a loop that scheduling must break, and that settles
  // once 'vb' selects 'ca'. Its values are not checked: IEEE 1800-2023 25.9 does not allow
  // members through virtual interfaces in sensitivity lists, so simulators differ on whether @*
  // is sensitive to them.
  cbus ca (), cb ();
  virtual cbus va = ca, vb = cb;
  // verilator lint_off UNOPTFLAT
  logic [7:0] y;
  // verilator lint_on UNOPTFLAT
  always @* va.x = y;
  always @* y = vb.x;
  initial #42 vb = ca;

  // A process sensitive to a member through a virtual interface is evaluated again when the
  // member changes. It reads the member, which is not in its sensitivity list, so V3Active does
  // not make it combinational logic.
  bus e ();
  virtual bus ve = e;
  logic [7:0] seen_e;
  always @(ve.y) begin
    seen_e = ve.y * 8'd3;
    if (seen_e > 8'd5) seen_e = seen_e - 8'd1;
  end

  // A blocking write through a virtual interface to some bits in combinational logic, and NBAs
  // to the other bits, which do not overlap
  pbus p ();
  virtual pbus vp = p;
  logic [3:0] lo;
  always @* vp.y[3:0] = lo;

  // Writes through a virtual interface between a write and a read of the member, which must not
  // read the first write: an assignment, $sscanf, and a concatenation
  wbus w ();
  virtual wbus vw = w;
  int s1, s2, s3;
  always @(posedge clk) begin
    w.x1 = 5;
    vw.x1 = cyc;
    s1 <= w.x1;
    w.x2 = 5;
    void'($sscanf("7", "%d", vw.x2));
    s2 <= w.x2;
    w.x3 = 5;
    {vw.x3[7:4], vw.x3[3:0]} = 8'h21;
    s3 <= w.x3;
  end

  // A member forced and released, and read through a virtual interface
  bus fo ();
  virtual bus vfo = fo;
  logic [7:0] seen_fo;
  initial begin
    fo.y = 8'd1;
    force fo.y = 8'd2;
    #1 release fo.y;
    fo.y = 8'd3;
    #1 seen_fo = vfo.y;
  end

  // A task that is not inlined, as an argument by reference is not a variable, and that writes
  // through a virtual interface: the handle is its argument, so the task is not impure
  bus ni ();
  virtual bus vni = ni;
  logic [7:0] ra[2];
  task automatic put(virtual bus v, ref logic [7:0] r);
    v.y = r;
  endtask
  initial begin
    ra[1] = 8'd9;
    put(vni, ra[1]);
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    cb.x = 8'(cyc);
    e.y <= 8'(cyc);
    lo <= 4'(cyc);
    p.y[7:4] <= 4'(cyc);
  end

  always @(negedge clk) begin
    if (cyc >= 1) begin
      `checkd(seen_e, e.y * 8'd3 > 8'd5 ? e.y * 8'd3 - 8'd1 : e.y * 8'd3);
      `checkd(p.y, {4'(cyc - 1), 4'(cyc - 1)});
      `checkd(s1, cyc - 1);
      `checkd(s2, 7);
      `checkd(s3, 33);
      `checkd(seen_fo, 8'd3);
      `checkd(ni.y, 8'd9);
    end
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
