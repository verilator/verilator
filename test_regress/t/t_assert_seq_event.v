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
  bit a, b, c;
  bit a1, a2, a3, b1;
  int cyc;
  int seq_hits, seq_hits2, ref_hits, one_hits, dc_hits;
  int rng_hits, rng_ref;

  // verilog_format: off  // verible does not support clocking events inside sequence declarations
  sequence seq;
    @(posedge clk) a ##1 b ##1 c;
  endsequence

  sequence seq_one;
    @(posedge clk) a;
  endsequence

  sequence seq_rng;
    @(posedge clk) a ##[1:3] b;
  endsequence
  // verilog_format: on

  // seq_dc inherits the default clocking; counts must match seq
  default clocking @(posedge clk);
  endclocking

  sequence seq_dc;
    a ##1 b ##1 c;
  endsequence

  // ref_hits and rng_ref are independent shift-register oracles;
  // simultaneous end points resume a blocked waiter once
  initial forever begin
    @seq;
    seq_hits = seq_hits + 1;
  end
  initial forever begin
    @seq;
    seq_hits2 = seq_hits2 + 1;
  end
  initial forever begin
    @seq_one;
    one_hits = one_hits + 1;
  end
  initial forever begin
    @seq_dc;
    dc_hits = dc_hits + 1;
  end
  initial forever begin
    @seq_rng;
    rng_hits = rng_hits + 1;
  end

  always @(posedge clk) begin
    if (a2 && b1 && c) ref_hits = ref_hits + 1;
    if (b && (a1 || a2 || a3)) rng_ref = rng_ref + 1;
    a3 <= a2;
    a2 <= a1;
    a1 <= a;
    b1 <= b;
  end

  // a/b/c bit spacing exceeds the ##2 window to decorrelate the LFSR taps
  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[30:0], crc[31] ^ crc[21] ^ crc[1] ^ crc[0]};
    a <= crc[0];
    b <= crc[4];
    c <= crc[8];
    if (cyc == 60) $finish;
  end

  // Counts read in final (Postponed) to avoid same-timestep races.
  final begin
    `checkd(seq_hits, 14);
    `checkd(seq_hits2, 14);
    `checkd(ref_hits, 14);
    `checkd(one_hits, 30);
    `checkd(dc_hits, 14);
    `checkd(rng_hits, 26);
    `checkd(rng_ref, 26);
    $write("*-* All Finished *-*\n");
  end
endmodule
