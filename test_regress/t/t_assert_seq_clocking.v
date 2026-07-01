// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
  input clk
);
  int unsigned crc = 32'h1;
  bit a, b;
  int cyc = 0;
  int fails_single = 0;
  int fails_multi = 0;

  // verilog_format: off  // verible does not support clocking events inside sequence declarations
  sequence s_single;
    @(posedge clk) a
  endsequence

  sequence s_multi;
    @(posedge clk) (a ##1 b);
  endsequence

  sequence s_unused;
    @(posedge clk) b;
  endsequence
  // verilog_format: on

  ap_single: assert property (s_single) else fails_single = fails_single + 1;
  ap_multi: assert property (s_multi) else fails_multi = fails_multi + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[30:0], crc[31] ^ crc[21] ^ crc[1] ^ crc[0]};
    a <= crc[0];
    b <= crc[1];
    if (cyc == 40) $finish;
  end

  // Counts read in final (Postponed) to avoid same-timestep races.
  // Concrete Verilator counts; Questa: fails_single=17 fails_multi=17
  final begin
    `checkd(fails_single, 17);
    `checkd(fails_multi, 17);
    $write("*-* All Finished *-*\n");
  end
endmodule
