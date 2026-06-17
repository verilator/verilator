// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

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
    @(posedge clk) a;
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
  // Concrete Verilator counts; cross-checked equal in Questa 2022.3
  // on the self-clocked equivalent (same CRC stimulus).
  // Questa: fails_single=17 fails_multi=17
  final begin
    if (fails_single == 17 && fails_multi == 17) begin
      $write("*-* All Finished *-*\n");
    end else begin
      $write("FAILED fails_single=%0d fails_multi=%0d\n", fails_single, fails_multi);
      $stop;
    end
  end
endmodule
