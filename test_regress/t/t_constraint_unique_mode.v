// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// A 'unique' constraint takes part in constraint_mode(), and a 'unique' over a
// typedef'd array resolves through the typedef.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

typedef bit [1:0] arr_t[4];

class C;
  rand arr_t arr;

  constraint uniq {unique {arr};}
endclass

module t;
  initial begin
    automatic C c = new;
    int ok;

    // Four distinct 2-bit values are a permutation of 0..3
    for (int i = 0; i < 10; ++i) begin
      ok = c.randomize();
      `checkd(ok, 1);
      foreach (c.arr[j]) foreach (c.arr[k]) if (j != k) `checkh(c.arr[j] == c.arr[k], 1'b0);
    end
    ok = c.randomize() with {arr[0] == arr[1];};
    `checkd(ok, 0);

    // Disabled, the array is unconstrained
    c.uniq.constraint_mode(0);
    ok = c.randomize() with {arr[0] == arr[1];};
    `checkd(ok, 1);

    // Enabled again, distinctness is back
    c.uniq.constraint_mode(1);
    ok = c.randomize() with {arr[0] == arr[1];};
    `checkd(ok, 0);
    for (int i = 0; i < 10; ++i) begin
      ok = c.randomize();
      `checkd(ok, 1);
      foreach (c.arr[j]) foreach (c.arr[k]) if (j != k) `checkh(c.arr[j] == c.arr[k], 1'b0);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
