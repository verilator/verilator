// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// disable iff mid-window on the counter-FSM path (##[1:N], N > 256 unroll limit).

module t (
    input clk
);
  localparam int N = 257;  // > 256 unroll limit -> counter FSM path
  localparam int PERIOD = 260;  // > N -> attempts never overlap
  localparam int NATT = 30;

  int cyc = 0;
  reg [63:0] crc = 64'h5aef0c8d_d70a4497;

  int phase = 0;
  int idx = 0;
  wire in_run = (idx < NATT);
  wire trig = in_run && (phase == 0);
  wire value = 1'b0;

  reg do_dis = 0;
  int dis_at = 0;
  wire dis = in_run && do_dis && (phase == dis_at);

  int n_dis_fire = 0;
  int n_ctrl_fire = 0;
  int exp_dis_fire = 0;

  assert property (@(posedge clk) disable iff (dis) trig |-> ##[1:N] value)
  else n_dis_fire <= n_dis_fire + 1;

  assert property (@(posedge clk) disable iff (1'b0) trig |-> ##[1:N] value)
  else n_ctrl_fire <= n_ctrl_fire + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (phase == PERIOD - 1) begin
      phase <= 0;
      idx <= idx + 1;
    end else begin
      phase <= phase + 1;
    end
    if (phase == 0) begin
      do_dis <= crc[3];
      dis_at <= 1 + (int'(crc[20:12]) % (N - 1));
    end
    if (in_run && phase == N && !do_dis) exp_dis_fire <= exp_dis_fire + 1;
    if (idx == NATT && phase == 4) begin
`ifdef TEST_VERBOSE
      $write("n_dis_fire=%0d exp=%0d n_ctrl_fire=%0d\n", n_dis_fire, exp_dis_fire, n_ctrl_fire);
`endif
      `checkd(n_dis_fire, exp_dis_fire);
      `checkd(n_ctrl_fire, NATT);
      if (n_dis_fire == 0 || n_dis_fire == NATT) $stop;  // guard a degenerate seed
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
