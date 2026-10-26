// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// $isunbounded() on a plain variable always folds to false; this triggers
// a suppressible CONSTRAINTIGN warning (see t_constraint_isunbounded.v for
// the suppressed case), but still compiles and runs correctly.
class C;
  rand int x;
  constraint c {
    !$isunbounded(x);
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
      if (ok != 1) $stop;
      if (obj.x < 1 || obj.x > 10) begin
        $write("%%Error: x out of range: %0d\n", obj.x);
        $stop;
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
