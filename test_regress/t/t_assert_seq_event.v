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
  int seq_hits = 0, seq_hits2 = 0, ref_hits = 0, one_hits = 0, dc_hits = 0;

  // verilog_format: off  // verible does not support clocking events inside sequence declarations
  sequence seq;
    @(posedge clk) a ##1 b ##1 c;
  endsequence

  sequence seq_one;
    @(posedge clk) a;
  endsequence
  // verilog_format: on

  // seq_dc has no clocking event, so it inherits the default clocking and must
  // behave identically to the explicitly-clocked seq above.
  default clocking @(posedge clk);
  endclocking

  sequence seq_dc;
    a ##1 b ##1 c;
  endsequence

  // A sequence used as an `@` event control resumes once per sequence end point
  // (IEEE 1800-2023 9.4.2.4). seq_hits/seq_hits2 are two waiters on the same
  // multi-cycle sequence; ref_hits is an independent shift-register oracle (end
  // point at posedge N when a@N-2, b@N-1, c@N); one_hits is the single-cycle case.
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

  always @(posedge clk) begin
    if (a2 && b1 && c) ref_hits = ref_hits + 1;
    a2 <= a1;
    a1 <= a;
    b1 <= b;
  end

  // a/b/c are spaced to crc[0]/crc[4]/crc[8] -- past the ##2 window -- so the
  // left-shift LFSR cannot correlate a@T, b@T+1, c@T+2 into one bit; otherwise
  // the multi-cycle end-point machinery would collapse into a triviality.
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
    $write("*-* All Finished *-*\n");
  end
endmodule
