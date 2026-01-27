// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Base;
endclass
class ExbaseA extends Base;
endclass
class ExbaseB extends Base;
endclass

module t;
  int i;

  Base b;
  ExbaseA ba, ba1;
  ExbaseB bb, bb1;

  initial begin
    ba = new;
    b = ba;
    i = $cast(ba1, b);
    if (i != 1) $stop;
    $cast(ba1, b);  // ok at runtime

    b = null;
    $cast(ba1, b);  // no failure on null

    bb = new;
    b = bb;
    i = $cast(ba1, b);
    if (i != 0) $stop;
    void'($cast(ba1, b));  // ok as is function
    $cast(ba1, b);  // <-- Bad $cast task

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
