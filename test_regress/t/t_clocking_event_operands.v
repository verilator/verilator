// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Clocking events with dotted and package-scope names (IEEE 1800-2023 A.6.5)
package p;
  logic clk = 0;
endpackage

module t;
  typedef struct packed {
    logic clk;
    logic other;
  } clk_t;
  clk_t sc = '0;
  logic a = 0;
  int n_dcb = 0;
  int n_cpkg = 0;

  default clocking dcb @sc.clk; endclocking
  clocking cpkg @p::clk; endclocking

  covergroup cg_sc @sc.clk;
    coverpoint a;
  endgroup
  cg_sc cg_sc_inst = new;

  covergroup cg_pkg @p::clk;
    coverpoint a;
  endgroup
  cg_pkg cg_pkg_inst = new;

  always @(dcb) n_dcb++;
  always @(cpkg) n_cpkg++;

  int n_root = 0;
  clocking croot @$root.t.a; endclocking
  always @(croot) n_root++;

  for (genvar i = 0; i < 2; i++) begin : g
    logic clk = 0;
  end
  int n_gen = 0;
  clocking cgen @g[1].clk; endclocking
  always @(cgen) n_gen++;

  initial begin
    #1 sc.clk = 1;
    #1 a = 1;
    sc.other = 1;
    #1 sc.clk = 0;
    #1 p::clk = 1;
    #1 g[0].clk = 1;
    #1 g[1].clk = 1;
    #1 $finish;
  end

  final begin
    `checkd(n_dcb, 2);
    `checkd(n_cpkg, 1);
    `checkd(n_root, 1);
    `checkd(n_gen, 1);
    `checkr(cg_sc_inst.get_inst_coverage(), 100.0);
    `checkr(cg_pkg_inst.get_inst_coverage(), 50.0);
    $write("*-* All Finished *-*\n");
  end
endmodule
