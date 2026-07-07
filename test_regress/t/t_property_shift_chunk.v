// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// ##N delay and held[*N] repetition pack shift chains across 64-bit chunks;
// the completion must land on exactly cycle N (off-by-one brackets fail).

module t (
    input clk
);
  localparam int LEN = 130;
  localparam int PERIOD = 140;
  localparam int NATT = 12;

  int cyc = 0;
  reg [63:0] crc = 64'h5aef0c8d_d70a4497;

  int phase = 0;
  int idx = 0;
  wire in_run = (idx < NATT);
  wire trig = in_run && (phase == 0);

  reg res_fail = 0;
  reg rep_fail = 0;
  wire res = in_run && (phase == LEN) && !res_fail;
  wire rep_res = in_run && (phase == LEN) && !rep_fail;
  wire held = in_run && (phase <= LEN - 1);

  int n_d129 = 0;
  int n_d130 = 0;
  int n_d131 = 0;
  int n_rok = 0;
  int n_rbad = 0;
  int exp_d130 = 0;
  int exp_rok = 0;

  assert property (@(posedge clk) trig |-> ##(LEN-1) res)
  else n_d129 <= n_d129 + 1;
  assert property (@(posedge clk) trig |-> ##LEN res)
  else n_d130 <= n_d130 + 1;
  assert property (@(posedge clk) trig |-> ##(LEN+1) res)
  else n_d131 <= n_d131 + 1;

  assert property (@(posedge clk) trig |-> held[*LEN] ##1 rep_res)
  else n_rok <= n_rok + 1;
  assert property (@(posedge clk) trig |-> held[*(LEN + 1)] ##1 rep_res)
  else n_rbad <= n_rbad + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (phase == PERIOD - 1) begin
      phase <= 0;
      idx <= idx + 1;
    end
    else begin
      phase <= phase + 1;
    end
    if (phase == 0) begin
      res_fail <= crc[2];
      rep_fail <= crc[9];
    end
    if (in_run && phase == LEN) exp_d130 <= exp_d130 + (res_fail ? 1 : 0);
    if (in_run && phase == LEN) exp_rok <= exp_rok + (rep_fail ? 1 : 0);
    if (idx == NATT && phase == 4) begin
`ifdef TEST_VERBOSE
      $write("d129=%0d d130=%0d exp=%0d d131=%0d rok=%0d exp=%0d rbad=%0d\n", n_d129, n_d130,
             exp_d130, n_d131, n_rok, exp_rok, n_rbad);
`endif
      `checkd(n_d129, NATT);
      `checkd(n_d130, exp_d130);
      `checkd(n_d131, NATT);
      `checkd(n_rok, exp_rok);
      `checkd(n_rbad, NATT);
      if (exp_d130 == 0 || exp_d130 == NATT) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
