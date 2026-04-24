// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (/*AUTOARG*/
    // Inputs
    clk
);

  input clk;

  bit [63:0] crc = 64'h5aef0c8d_d70a4497;
  int cyc = 0;
  logic a_high = 1'b1;
  logic a_low = 1'b0;
  wire a_rand = crc[0];
  wire rst_rand = crc[5];

  int high_bounded_fail = 0;
  int high_sbounded_fail = 0;
  int high_degenerate_fail = 0;
  int low_bounded_pass = 0;
  int low_degenerate_pass = 0;
  int rand_bounded_pass = 0;
  int rand_bounded_fail = 0;
  int disable_bounded_pass = 0;
  int disable_bounded_fail = 0;

  assert property (@(posedge clk) always 1'b1);

  assert property (@(posedge clk) always [0:3] a_high)
  else
    high_bounded_fail++;

  assert property (@(posedge clk) s_always [1:2] a_high)
  else
    high_sbounded_fail++;

  assert property (@(posedge clk) always [0:0] a_high)
  else
    high_degenerate_fail++;

  assert property (@(posedge clk) always [0:3] a_low)
    low_bounded_pass++;

  assert property (@(posedge clk) always [0:0] a_low)
    low_degenerate_pass++;

  assert property (@(posedge clk) always [0:3] a_rand)
    rand_bounded_pass++;
  else
    rand_bounded_fail++;

  // Same antecedent but killed by rst_rand: disable iff reduces attempt count.
  assert property (@(posedge clk) disable iff (rst_rand) always [0:3] a_rand)
    disable_bounded_pass++;
  else
    disable_bounded_fail++;

  property p_always_true;
    @(posedge clk) always (1'b1);
  endproperty
  assert property (p_always_true);

  property p_disable_named;
    @(posedge clk) disable iff (rst_rand) always [1:2] a_high;
  endproperty
  assert property (p_disable_named);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 99) begin
      `checkd(high_bounded_fail, 0);
      `checkd(high_sbounded_fail, 0);
      `checkd(high_degenerate_fail, 0);
      `checkd(low_bounded_pass, 0);
      `checkd(low_degenerate_pass, 0);
      `checkd(rand_bounded_pass, 3);
      `checkd(rand_bounded_fail, 97);
      `checkd(disable_bounded_pass, 2);
      `checkd(disable_bounded_fail, 70);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
