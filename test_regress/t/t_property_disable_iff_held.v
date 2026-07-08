// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// IEEE 1800-2023 16.12: a disable iff condition held continuously true must
// disable every attempt of a multi-cycle property (verilator/verilator#7792).
// en_held is a plain non-$sampled, non-constant signal held 1, so it exercises
// the NFA disable-counter path. The held assert/cover must never fire; the
// `disable iff (1'b0)` controls prove the same assert/cover do fire when enabled.

module t (
    input clk
);
  int cyc = 0;
  reg [63:0] crc = 64'h5aef0c8d_d70a4497;
  wire a = crc[0];
  wire b = crc[4];

  bit en_held = 1'b1;

  int n_held_assert = 0;
  int n_held_cover = 0;
  int n_ctrl_assert = 0;
  int n_ctrl_cover = 0;

  // Held-true disable: assert + cover must be fully suppressed.
  assert property (@(posedge clk) disable iff (en_held) (a ##1 b))
    else n_held_assert <= n_held_assert + 1;
  cover property (@(posedge clk) disable iff (en_held) (a ##1 b))
    n_held_cover <= n_held_cover + 1;

  // Enabled control (disable iff 1'b0): same assert + cover must fire.
  assert property (@(posedge clk) disable iff (1'b0) (a ##1 b))
    else n_ctrl_assert <= n_ctrl_assert + 1;
  cover property (@(posedge clk) disable iff (1'b0) (a ##1 b))
    n_ctrl_cover <= n_ctrl_cover + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 99) begin
      `checkd(n_held_assert, 0);
      `checkd(n_held_cover, 0);
      `checkd(n_ctrl_assert, 58);
      `checkd(n_ctrl_cover, 26);  // Others: 26, One other: 0
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
