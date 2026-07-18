// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Mid-window disable pulse on the packed ##N delay path (N < unroll limit).

module t (
    input clk
);
  localparam int N = 8;
  localparam int PERIOD = 12;
  localparam int NATT = 40;

  int cyc = 0;
  reg [63:0] crc = 64'h5aef0c8d_d70a4497;

  int phase = 0;
  int idx = 0;
  wire in_run = (idx < NATT);
  wire trig = in_run && (phase == 0);

  reg do_dis = 0;
  int dis_at = 0;
  reg fail_now = 0;
  wire value = !(in_run && (phase == N) && fail_now);
  wire dis = in_run && do_dis && (phase == dis_at);

  int n_dis_fire = 0;
  int n_ctrl_fire = 0;
  int exp_dis_fire = 0;
  int exp_ctrl_fire = 0;

  assert property (@(posedge clk) disable iff (dis) trig |-> ##N value)
  else n_dis_fire <= n_dis_fire + 1;

  assert property (@(posedge clk) disable iff (1'b0) trig |-> ##N value)
  else n_ctrl_fire <= n_ctrl_fire + 1;

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
      do_dis <= crc[3];
      dis_at <= 1 + (int'(crc[20:12]) % (N - 1));
      fail_now <= crc[7];
    end
    if (in_run && phase == N) begin
      exp_ctrl_fire <= exp_ctrl_fire + (fail_now ? 1 : 0);
      if (!do_dis) exp_dis_fire <= exp_dis_fire + (fail_now ? 1 : 0);
    end
    if (idx == NATT && phase == 4) begin
`ifdef TEST_VERBOSE
      $write("n_dis_fire=%0d exp=%0d n_ctrl_fire=%0d exp_ctrl=%0d\n", n_dis_fire, exp_dis_fire,
             n_ctrl_fire, exp_ctrl_fire);
`endif
      `checkd(n_dis_fire, exp_dis_fire);
      `checkd(n_ctrl_fire, exp_ctrl_fire);
      if (n_dis_fire == 0 || n_dis_fire == NATT) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
