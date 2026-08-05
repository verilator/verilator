// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// A 'unique' nested in a constraint 'if' arm, over scalar rand members or over
// a statically sized array, applies only when the arm's condition holds.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

class C;
  rand bit [1:0] x, y, z;
  rand bit sel;

  constraint c {
    if (sel) {
      unique {x, y, z};
    } else {
      unique {x, y};
    }
  }
endclass

class A;
  rand bit [1:0] arr[4];
  rand bit [1:0] one[1];
  rand bit sel;

  constraint c {
    if (sel) {
      unique {arr};
      // A single element is trivially unique
      unique {one};
    }
  }
endclass

module t;
  initial begin
    automatic C c = new;
    automatic A a = new;
    int ok;

    // The 'then' arm holds: its operands are pairwise distinct
    for (int i = 0; i < 20; ++i) begin
      ok = c.randomize() with {sel == 1;};
      `checkd(ok, 1);
      `checkh(c.x == c.y, 1'b0);
      `checkh(c.x == c.z, 1'b0);
      `checkh(c.y == c.z, 1'b0);
    end
    // and cannot be violated
    ok = c.randomize() with {
      sel == 1;
      x == y;
    };
    `checkd(ok, 0);

    // The 'else' arm holds: only its own operands are constrained
    for (int i = 0; i < 20; ++i) begin
      ok = c.randomize() with {sel == 0;};
      `checkd(ok, 1);
      `checkh(c.x == c.y, 1'b0);
    end
    ok = c.randomize() with {
      sel == 0;
      y == z;
    };
    `checkd(ok, 1);
    ok = c.randomize() with {
      sel == 0;
      x == y;
    };
    `checkd(ok, 0);

    // An array 'unique' under the same guard: four distinct 2-bit values are a
    // permutation of 0..3, and are unconstrained once the guard is false
    for (int i = 0; i < 20; ++i) begin
      ok = a.randomize() with {sel == 1;};
      `checkd(ok, 1);
      foreach (a.arr[j]) foreach (a.arr[k]) if (j != k) `checkh(a.arr[j] == a.arr[k], 1'b0);
    end
    ok = a.randomize() with {
      sel == 1;
      arr[0] == arr[1];
    };
    `checkd(ok, 0);
    ok = a.randomize() with {
      sel == 0;
      arr[0] == arr[1];
    };
    `checkd(ok, 1);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
