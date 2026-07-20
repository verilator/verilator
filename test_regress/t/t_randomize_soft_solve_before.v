// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class solve_before_soft_c;
  rand bit sel;
  rand int unsigned m;
  rand int unsigned x;
  constraint m_soft {soft m == 7;}
  constraint sb_cons {
    solve sel before x;
    if (sel)
    x == 0;
    else
    x inside {[1 : 100]};
  }
endclass

class conflicting_soft_c;
  rand bit sel;
  rand int unsigned a;
  rand int unsigned b;
  constraint a_soft3 {soft a == 3;}
  constraint a_soft9 {soft a == 9;}
  constraint sb_cons {
    solve sel before b;
    if (sel)
    b == 0;
    else
    b inside {[1 : 100]};
  }
endclass

module t;
  initial begin
    static solve_before_soft_c o1 = new();
    static conflicting_soft_c o2 = new();
    repeat (20) begin
      `checkd(o1.randomize(), 1)
      `checkd(o1.m, 32'd7)
    end
    repeat (20) begin
      `checkd(o2.randomize(), 1)
      `checkd(o2.a, 32'd9)
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
