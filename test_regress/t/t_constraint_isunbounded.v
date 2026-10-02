// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// $isunbounded(x) on a plain variable always folds to false, so !$isunbounded(x)
// is an always-true constraint that shouldn't affect x's range at all.
class C;
  rand int x;
  constraint c {
    // verilator lint_off CONSTRAINTIGN
    !$isunbounded(x);
    // verilator lint_on CONSTRAINTIGN
    x inside {[1 : 10]};
  }
endclass

module t;
  initial begin
    C obj;
    int ok;
    obj = new;
    repeat (10) begin
      ok = obj.randomize();
      `checkd(ok, 1);
      if (obj.x < 1 || obj.x > 10) begin
        $write("%%Error: x out of range: %0d\n", obj.x);
        `stop;
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
