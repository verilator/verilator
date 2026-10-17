// DESCRIPTION: Verilator: Accesses through virtual interfaces refer only to the instances the
// virtual interfaces may point to, and are ordered before the NBA updates of those instances
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface bus (
    input bit clk
);
  logic [7:0] x = 0;
  logic [7:0] y;
  always @(posedge clk) x <= x + 1;
endinterface

module agent (
    input bit clk
);
  virtual bus v;
  logic [7:0] seen;
  always @(posedge clk) seen <= v.x;
endmodule

module t;
  bit clk;
  int cyc;
  always #5 clk = ~clk;

  // Each agent's virtual interface points to one instance of the array
  bus a[4] (.clk);
  virtual bus vs[4];
  initial begin
    vs = a;
    g[0].u.v = vs[0];
    g[1].u.v = vs[1];
    g[2].u.v = vs[2];
    g[3].u.v = vs[3];
  end
  for (genvar i = 0; i < 4; ++i) begin : g
    agent u (.clk);
  end

  // One instance, through a copy, and through elements assigned one by one
  virtual bus vc;
  virtual bus ve[2];
  initial begin
    #1 vc = g[1].u.v;
    ve[0] = a[2];
    ve[1] = a[3];
  end
  logic [7:0] seen_c, seen_e;
  always @(posedge clk) begin
    seen_c <= vc.x;
    seen_e <= ve[1].x;
    ve[0].y = 8'(cyc);
  end

  // Any instance, through a variable index, and an output argument
  task automatic get(output virtual bus o);
    o = vs[0];
  endtask
  int k = 2;
  virtual bus vk, vo;
  initial #1 begin
    vk = vs[k];
    get(vo);
  end
  logic [7:0] seen_k, seen_o;
  always @(posedge clk) begin
    seen_k <= vk.x;
    seen_o <= vo.x;
  end

  always @(posedge clk) cyc <= cyc + 1;
  always @(negedge clk) begin
    if (cyc >= 1) begin
      `checkd(g[0].u.seen, 8'(cyc - 1));
      `checkd(g[1].u.seen, 8'(cyc - 1));
      `checkd(g[2].u.seen, 8'(cyc - 1));
      `checkd(g[3].u.seen, 8'(cyc - 1));
      `checkd(seen_c, 8'(cyc - 1));
      `checkd(seen_e, 8'(cyc - 1));
      `checkd(a[2].y, 8'(cyc - 1));
      `checkd(seen_k, 8'(cyc - 1));
      `checkd(seen_o, 8'(cyc - 1));
    end
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
