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
  bit a1, a2, b1;
  int cyc = 0;
  int seq_hits = 0, seq_hits2 = 0, ref_hits = 0, one_hits = 0;

  // verilog_format: off  // verible does not support clocking events inside sequence declarations
  sequence seq;
    @(posedge clk) a ##1 b ##1 c;
  endsequence

  sequence seq_one;
    @(posedge clk) a;
  endsequence
  // verilog_format: on

  // Feature under test: a sequence referenced outside an assertion via the `@`
  // event control resumes once per sequence end point (IEEE 1800-2023 9.4.2.4).
  initial forever begin
    @seq;
    seq_hits = seq_hits + 1;
  end

  // A second waiter on the SAME sequence must see exactly the same end points.
  initial forever begin
    @seq;
    seq_hits2 = seq_hits2 + 1;
  end

  // Single-cycle sequence end point: resumes whenever `a` is sampled true.
  initial forever begin
    @seq_one;
    one_hits = one_hits + 1;
  end

  // Independent oracle: an end point lands at posedge N when the sampled values
  // give a at N-2, b at N-1, c at N.
  always @(posedge clk) begin
    if (a2 && b1 && c) ref_hits = ref_hits + 1;
    a2 <= a1;
    a1 <= a;
    b1 <= b;
  end

  // Bits a/b/c are spaced past the ##2 window (crc[0]/crc[4]/crc[8]) so the
  // left-shift LFSR does not correlate a@T, b@T+1, c@T+2 into one bit; the
  // multi-cycle end-point machinery is then genuinely exercised.
  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[30:0], crc[31] ^ crc[21] ^ crc[1] ^ crc[0]};
    a <= crc[0];
    b <= crc[4];
    c <= crc[8];
    if (cyc == 60) $finish;
  end

  // Counts read in final (Postponed) to avoid same-timestep races.
  // Concrete Verilator counts; Questa: seq_hits=14 ref_hits=14 one_hits=30
  final begin
    `checkd(seq_hits, ref_hits);
    `checkd(seq_hits2, seq_hits);
    `checkd(seq_hits, 14);
    `checkd(one_hits, 30);
    $write("*-* All Finished *-*\n");
  end
endmodule
