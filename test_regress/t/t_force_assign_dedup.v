// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jonathan Drolet
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define IMPURE_ONE |($random | $random)
// verilog_format: on

// Regression for V3Force: a design with both an explicit force/release
// target and an unrelated procedural continuous assign/deassign target
// makes forceAllImpl() and assignAllImpl() each build a
// '(en & val) | (~en & raw)' __VforceRd-maintenance formula. The second
// pass must reuse the raw-read protection the first pass already set up
// for 'a', not re-substitute it into a read of its own __VforceRd shadow -
// that would make the formula self-referential and freeze 'a' at its
// reset value.
module t;
  logic [7:0] a /* verilator forceable */;
  assign a = 8'hA5;

  logic b;

  initial begin
    if (`IMPURE_ONE == 0) force a = 8'h00;
    else release a;

    assign b = 1'b1;

    `checkh(a, 8'hA5);
    `checkh(b, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
