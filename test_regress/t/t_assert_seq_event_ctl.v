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
  bit a, b, rst;
  bit a1;
  int cyc;
  int hits, ref_hits, one_hits, one_ref;

  // Neither the default disable iff nor $assertoff may suppress a sequence event control
  default disable iff (rst);

  // verilog_format: off  // verible does not support clocking events inside sequence declarations
  sequence seq;
    @(posedge clk) a ##1 b;
  endsequence

  sequence seq_one;
    @(posedge clk) 1;
  endsequence
  // verilog_format: on

  initial begin
    $assertoff;
    #300 $assertkill;
  end

  initial forever begin
    @seq;
    hits = hits + 1;
  end
  initial forever begin
    @seq_one;
    one_hits = one_hits + 1;
  end

  always @(posedge clk) begin
    if (a1 && b) ref_hits = ref_hits + 1;
    one_ref = one_ref + 1;
    a1 <= a;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[30:0], crc[31] ^ crc[21] ^ crc[1] ^ crc[0]};
    a <= crc[0];
    b <= crc[4];
    rst <= crc[2];
  end

  always @(negedge clk) begin
    if (cyc == 60) $finish;
  end

  final begin
    `checkd(hits, ref_hits);
    `checkd(one_hits, one_ref);
    `checkd(hits, 19);
    `checkd(one_hits, 60);
    $write("*-* All Finished *-*\n");
  end
endmodule
