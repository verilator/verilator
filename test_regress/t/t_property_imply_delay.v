// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc;
  reg [63:0] crc;

  // Take CRC data and apply to testblock inputs
  // Use bits far apart (not adjacent) to break LFSR shift correlation,
  // ensuring ##1 and ##2 delay assertions see uncorrelated a/b values.
  wire a = crc[0];
  wire b = crc[4];

  int count_fail_overlap1 = 0;
  int count_fail_overlap2 = 0;
  int count_fail_nonoverlap = 0;

  // Overlapped implication with 1-cycle delay: a |-> ##1 b
  assert property (@(negedge clk) a |-> ##1 b)
  else count_fail_overlap1 = count_fail_overlap1 + 1;

  // Overlapped implication with 2-cycle delay: a |-> ##2 b
  assert property (@(negedge clk) a |-> ##2 b)
  else count_fail_overlap2 = count_fail_overlap2 + 1;

  // Non-overlapped: a |=> ##1 b (equivalent to a |-> ##2 b)
  assert property (@(negedge clk) a |=> ##1 b)
  else count_fail_nonoverlap = count_fail_nonoverlap + 1;

  // Test loop
  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x a=%b b=%b\n", $time, cyc, crc, a, b);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      // Setup
      crc <= 64'h5aef0c8d_d70a4497;
    end
    else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);

      // |=> ##1 is equivalent to |-> ##2
      `checkd(count_fail_nonoverlap, count_fail_overlap2);

      // Result check
      `checkd(count_fail_overlap1, 22);
      `checkd(count_fail_overlap2, 25);
      `checkd(count_fail_nonoverlap, 25);

      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
