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

  int count_fail_257 = 0;

  // All forms exceed the prior kConsRepLimit=256 in V3AssertNfa
  // buildConsRep; pre-fix they crashed at codegen
  // (V3AstNodeExpr.h Unexpected Call).

  // Antecedent: 257 consecutive 1's in a CRC bit are effectively impossible,
  // so the antecedent never holds and count_fail stays at 0.
  assert property (@(posedge clk) a [* 257] |-> b)
  else count_fail_257 <= count_fail_257 + 1;

  // Consequent SExpr forms (issue #7552 reporter shape). Cover (not assert)
  // sidesteps the NFA pending-rejects over-count that already affects
  // assert ##1 a[*N] when the consequent cannot complete before sim ends.
  cover property (@(posedge clk) b ##1 a [* 257]);
  cover property (@(posedge clk) b ##1 a [* 512]);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
    end
    else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      `checkd(count_fail_257, 0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
