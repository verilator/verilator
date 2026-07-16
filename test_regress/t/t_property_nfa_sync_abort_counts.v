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

  // These multi-cycle counts are a nonvacuous-attempt oracle.
  initial $assertvacuousoff;

  int cyc;
  reg [63:0] crc;

  // Non-adjacent CRC bits to avoid LFSR shift correlation
  wire a = crc[0];
  wire b = crc[4];
  wire cnd_a = crc[8];
  wire cnd_r = crc[12];

  int multi_pass_pair1 = 0;
  int multi_fail_pair1 = 0;
  int multi_pass_pair2 = 0;
  int multi_fail_pair2 = 0;
  int multi_pass_nested = 0;
  int multi_fail_nested = 0;

  // Multi-cycle sync abort forms; accept-forced passes suppressed by $assertvacuousoff.
  assert property (@(posedge clk) sync_accept_on (cnd_a) (a |-> ##1 b)) multi_pass_pair1++;
  else multi_fail_pair1++;

  assert property (@(posedge clk) sync_reject_on (cnd_r) (a |-> b))
  else multi_fail_pair1++;

  assert property (@(posedge clk) sync_accept_on (cnd_a) b) multi_pass_pair2++;
  else multi_fail_pair2++;

  assert property (@(posedge clk) sync_reject_on (cnd_r) (a |-> ##2 b)) multi_pass_pair2++;
  else multi_fail_pair2++;

  assert property (@(posedge clk) sync_accept_on (cnd_a) sync_reject_on (cnd_r) (a |-> b))
    multi_pass_nested++;
  else multi_fail_nested++;

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x a=%b b=%b cnd_a=%b cnd_r=%b\n", $time, cyc, crc, a, b, cnd_a,
           cnd_r);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
    end
    else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      `checkd(multi_pass_pair1, 5);  // Other simulator: 42
      `checkd(multi_fail_pair1, 65);  // Other simulator: 39
      `checkd(multi_pass_pair2, 24);  // Other simulator: 74
      `checkd(multi_fail_pair2, 99);  // Other simulator: 73
      `checkd(multi_pass_nested, 7);  // Other simulator: 30
      `checkd(multi_fail_nested, 27);  // Other simulator: 18
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
