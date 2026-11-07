// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package p;
  logic clk = 0;
endpackage

module t (
  input clk
);
  int unsigned crc = 32'h1;
  bit a, b;
  int cyc = 0;
  int fails_single = 0;
  int fails_multi = 0;
  int fails_changed = 0;
  int fails_pkg = 0;
  int fails_pkg_seq = 0;
  int fails_concat = 0;

  // verilog_format: off  // verible does not support clocking events inside sequence declarations
  sequence s_single;
    @(posedge clk) a
  endsequence

  sequence s_multi;
    @(posedge clk) (a ##1 b);
  endsequence

  sequence s_changed;
    @clk a
  endsequence

  // Package-scope clocking event (IEEE 1800-2023 A.9.3)
  sequence s_pkg;
    @p::clk a
  endsequence

  sequence s_concat;
    @(posedge {{2{b, clk}}, {0{b}}}) a
  endsequence

  sequence s_unused;
    @(posedge clk) b;
  endsequence
  // verilog_format: on

  ap_single: assert property (s_single) else fails_single = fails_single + 1;
  ap_multi: assert property (s_multi) else fails_multi = fails_multi + 1;
  ap_changed: assert property (s_changed) else fails_changed = fails_changed + 1;
  ap_pkg: assert property (@p::clk a) else fails_pkg = fails_pkg + 1;
  ap_pkg_seq: assert property (s_pkg) else fails_pkg_seq = fails_pkg_seq + 1;
  ap_concat: assert property (s_concat) else fails_concat = fails_concat + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[30:0], crc[31] ^ crc[21] ^ crc[1] ^ crc[0]};
    a <= crc[0];
    b <= crc[1];
    p::clk <= ~p::clk;
    if (cyc == 40) $finish;
  end

  // Counts read in final (Postponed) to avoid same-timestep races.
  final begin
    `checkd(fails_single, 17);  // Other sims: 0
    `checkd(fails_multi, 17);  // Other sims: 0
    `checkd(fails_changed, 33);
    `checkd(fails_pkg, fails_pkg_seq);
    `checkd(fails_pkg > 0, 1);
    `checkd(fails_concat, fails_single);
    $write("*-* All Finished *-*\n");
  end
endmodule
