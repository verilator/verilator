// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

// Soft constraint relaxation must preserve the maximum compatible set.
// When soft[1] conflicts with soft[2], a correct algorithm should still
// keep soft[0] if it is compatible with soft[2].
//
// soft[0]: b > 100   (low priority, COMPATIBLE with soft[2])
// soft[1]: a == 30   (mid priority, CONFLICTS with soft[2])
// soft[2]: a == 80   (high priority, should win over soft[1])
//
// Correct result: a == 80, b > 100 (soft[0] and soft[2] both kept)
// Bug result:     a == 80, b unconstrained (soft[0] wrongly dropped)

class SoftRelax;
  rand bit [7:0] a;
  rand bit [7:0] b;
  constraint c_hard { a < 8'd200; b < 8'd200; }
  constraint c_soft0 { soft b > 8'd100; }
  constraint c_soft1 { soft a == 8'd30; }
  constraint c_soft2 { soft a == 8'd80; }
endclass

module t;
  initial begin
    SoftRelax obj;
    obj = new;
    repeat (20) begin
      `checkd(obj.randomize(), 1)
      `checkd(obj.a, 8'd80)
      `check_range(obj.b, 8'd101, 8'd199)
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
