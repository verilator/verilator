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
  wire cons_a = cyc < 1100;
  wire goto_a = cyc[1:0] != 0;

  int count_fail_257 = 0;
  int count_fail_cycles_513 = 0;
  int count_fail_threads_513 = 0;
  int count_fail_consrep_1025 = 0;
  int count_fail_consrep_range_1025 = 0;
  int count_fail_goto_1025 = 0;
  int count_fail_goto_range_1025 = 0;
  int count_cover_1025 = 0;

  // All N > prior kConsRepLimit=256 (pre-fix: V3AssertNfa crash at codegen).
  assert property (@(posedge clk) a [* 257] |-> b)
  else count_fail_257 <= count_fail_257 + 1;

  assert property (@(posedge clk) c |-> ##1 a [* 513])
  else count_fail_cycles_513 <= count_fail_cycles_513 + 1;

  // A blocking action counts all live threads rejected when the long run ends.
  assert property (@(posedge clk) cons_a [* 513])
  else if (cyc == 1100) count_fail_threads_513++;

  // One triggered attempt makes an off-by-one ring exit observable. Consecutive
  // repetition sees a long run; goto repetition advances across regular gaps.
  assert property (@(posedge clk) (cyc == 0) ##0 cons_a [* 1025: $] |-> cyc == 2047)
  else count_fail_consrep_1025++;
  assert property (@(posedge clk) (cyc == 0) ##0 cons_a [* 1: 1025] |-> cyc == 2047)
  else count_fail_consrep_range_1025++;
  cover sequence (@(posedge clk) a [* 1: 1025]) count_cover_1025++;

  assert property (@(posedge clk) (cyc == 0) ##0 goto_a [-> 1025] |-> cyc != 1366)
  else count_fail_goto_1025++;
  assert property (@(posedge clk) (cyc == 0) ##0 goto_a [-> 1: 1025] |-> cyc == 2047)
  else count_fail_goto_range_1025++;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
    end
    else if (cyc == 2047) begin
      `checkh(crc, 64'h91bd2213af2ba46e);
      `checkd(count_fail_257, 0);
      `checkd(count_fail_cycles_513, 666);
      `checkd(count_fail_threads_513, 513);
      `checkd(count_fail_consrep_1025, 76);
      `checkd(count_fail_consrep_range_1025, 1025);
      `checkd(count_fail_goto_1025, 1);
      `checkd(count_fail_goto_range_1025, 1025);
      `checkd(count_cover_1025, 2049);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
