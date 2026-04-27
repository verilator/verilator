// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  bit [63:0] crc = 64'h5aef0c8d_d70a4497;
  int cyc = 0;
  logic a_high = 1'b1;
  logic a_low = 1'b0;
  wire a_rand = crc[0];
  wire rst_rand = crc[5];

  // Per-assertion queues record the simulation cyc on each pass / else fire.
  // For "always [m:n] P" the action runs at cyc=K+n on success and at the
  // detected-violation cyc on failure -- both deterministic given the inputs.
  int high_bounded_pass_q[$];
  int high_sbounded_pass_q[$];
  int high_degenerate_pass_q[$];
  int low_bounded_fail_q[$];
  int low_degenerate_fail_q[$];
  int rand_bounded_pass_q[$];
  int rand_bounded_fail_q[$];
  int disable_bounded_pass_q[$];
  int disable_bounded_fail_q[$];

  // Bare always (collapses to immediate P).
  assert property (@(posedge clk) always 1'b1);

  // Bounded weak always over constant-true input.
  assert property (@(posedge clk) always [0:3] a_high) high_bounded_pass_q.push_back(cyc);

  // Bounded strong s_always over constant-true input.
  assert property (@(posedge clk) s_always [1:2] a_high) high_sbounded_pass_q.push_back(cyc);

  // Degenerate [0:0]: equivalent to immediate sample.
  assert property (@(posedge clk) always [0:0] a_high) high_degenerate_pass_q.push_back(cyc);

  // Constant-false: every attempt fails.
  assert property (@(posedge clk) always [0:3] a_low)
    ;
  else low_bounded_fail_q.push_back(cyc);

  assert property (@(posedge clk) always [0:0] a_low)
    ;
  else low_degenerate_fail_q.push_back(cyc);

  // CRC-driven random input: window [cyc..cyc+3] of a_rand.
  assert property (@(posedge clk) always [0:3] a_rand) rand_bounded_pass_q.push_back(cyc);
  else rand_bounded_fail_q.push_back(cyc);

  // disable iff suppresses attempts whose start cyc has rst_rand=1.
  assert property (@(posedge clk) disable iff (rst_rand) always [0:3] a_rand)
    disable_bounded_pass_q.push_back(cyc);
  else disable_bounded_fail_q.push_back(cyc);

  // Bare always inside named property.
  property p_always_true;
    @(posedge clk) always (1'b1);
  endproperty
  assert property (p_always_true);

  // disable iff inside named property.
  property p_disable_named;
    @(posedge clk) disable iff (rst_rand) always [1:2] a_high;
  endproperty
  assert property (p_disable_named);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 19) begin
      // Constant-true window [0:3]: K=0..16 succeed at cyc K+3 = 3..19.
      `checkd(high_bounded_pass_q.size(), 17);
      `checkd(high_bounded_pass_q[0], 3);
      `checkd(high_bounded_pass_q[$], 19);
      // Strong [1:2]: K=0..17 succeed at cyc K+2 = 2..19.
      `checkd(high_sbounded_pass_q.size(), 18);
      `checkd(high_sbounded_pass_q[0], 2);
      `checkd(high_sbounded_pass_q[$], 19);
      // Degenerate [0:0]: K=0..19 succeed at cyc K = 0..19.
      `checkd(high_degenerate_pass_q.size(), 20);
      `checkd(high_degenerate_pass_q[0], 0);
      `checkd(high_degenerate_pass_q[$], 19);
      // Constant-false: every attempt fails immediately.
      `checkd(low_bounded_fail_q.size(), 20);
      `checkd(low_degenerate_fail_q.size(), 20);
      // CRC + disable streams: counts pinned (cross-checked against Questa).
      `checkd(rand_bounded_pass_q.size(), 0);
      `checkd(rand_bounded_fail_q.size(), 20);
      `checkd(disable_bounded_pass_q.size(), 0);
      `checkd(disable_bounded_fail_q.size(), 13);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
