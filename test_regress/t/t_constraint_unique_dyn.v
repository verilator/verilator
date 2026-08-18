// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// A 'unique' constraint holds over containers whose element count is only
// settled at randomize() time, and over an array it constrains on its own.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

class Sized;
  rand bit [3:0] q[$];
  rand bit [3:0] d[];

  constraint sz {
    q.size() == 3;
    d.size() == 5;
  }
  constraint uniq {
    unique {q};
    unique {d};
  }
endclass

class Tiny;
  rand bit [3:0] q[$];

  constraint sz {q.size() == 1;}
  constraint uniq {unique {q};}
endclass

class Sole;
  rand bit [1:0] arr[4];

  constraint uniq {unique {arr};}
endclass

module t;
  initial begin
    automatic Sized sized = new;
    automatic Tiny tiny = new;
    automatic Sole sole = new;
    int ok;

    for (int n = 0; n < 10; ++n) begin
      ok = sized.randomize();
      `checkd(ok, 1);
      `checkd(sized.q.size(), 3);
      `checkd(sized.d.size(), 5);
      foreach (sized.q[i]) foreach (sized.q[j]) if (i != j) `checkh(sized.q[i] == sized.q[j], 1'b0);
      foreach (sized.d[i]) foreach (sized.d[j]) if (i != j) `checkh(sized.d[i] == sized.d[j], 1'b0);

      // A single element is trivially unique
      ok = tiny.randomize();
      `checkd(ok, 1);
      `checkd(tiny.q.size(), 1);

      // Four distinct 2-bit values are a permutation of 0..3
      ok = sole.randomize();
      `checkd(ok, 1);
      foreach (sole.arr[i])
      foreach (sole.arr[j]) if (i != j) `checkh(sole.arr[i] == sole.arr[j], 1'b0);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
