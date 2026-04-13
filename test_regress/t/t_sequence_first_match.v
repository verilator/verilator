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

  // Derive signals from non-adjacent CRC bits (avoid shift correlation)
  wire a = crc[0];
  wire b = crc[4];
  wire c = crc[8];
  wire d = crc[12];

  int count_fail1 = 0;
  int count_fail2 = 0;
  int count_fail3 = 0;
  int count_fail4 = 0;
  int count_fail5 = 0;
  int count_fail6 = 0;

  // Test 1: first_match with simple boolean
  assert property (@(posedge clk) first_match(a) |-> a)
    else count_fail1 <= count_fail1 + 1;

  // Test 2: first_match with boolean OR
  assert property (@(posedge clk) first_match(a or b) |-> (a | b))
    else count_fail2 <= count_fail2 + 1;

  // Test 3: first_match with boolean AND
  assert property (@(posedge clk) first_match(a and b) |-> (a & b))
    else count_fail3 <= count_fail3 + 1;

  // Test 4: nested first_match
  assert property (@(posedge clk) first_match(first_match(a)) |-> a)
    else count_fail4 <= count_fail4 + 1;

  // Test 5: first_match with boolean intersect
  assert property (@(posedge clk) first_match(a intersect b) |-> (a & b))
    else count_fail5 <= count_fail5 + 1;

  // Test 6: first_match in named sequence
  sequence s_fm;
    first_match(a and c);
  endsequence
  assert property (@(posedge clk) s_fm |-> (a & c))
    else count_fail6 <= count_fail6 + 1;

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x a=%b b=%b c=%b d=%b\n",
           $time, cyc, crc, a, b, c, d);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
    end
    else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      // All assertions are true by construction: antecedent implies consequent
      `checkd(count_fail1, 0);
      `checkd(count_fail2, 0);
      `checkd(count_fail3, 0);
      `checkd(count_fail4, 0);
      `checkd(count_fail5, 0);
      `checkd(count_fail6, 0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
