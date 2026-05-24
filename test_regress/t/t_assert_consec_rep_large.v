// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc;
  reg [63:0] crc;

  wire a = crc[0];
  wire b = crc[4];
  wire c = crc[8];

  int count_fail_257 = 0;
  int count_fail_513 = 0;

  // All N > prior kConsRepLimit=256 (pre-fix: V3AssertNfa crash at codegen).
  assert property (@(posedge clk) a [* 257] |-> b)
  else count_fail_257 <= count_fail_257 + 1;

  assert property (@(posedge clk) c |-> ##1 a [* 513])
  else count_fail_513 <= count_fail_513 + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
    end
    else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      `checkd(count_fail_257, 0);
      // Questa: 31 -- pre-existing ~26.5% NFA reject gap on |-> ##1 [*N]
      `checkd(count_fail_513, 23);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
