// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// Test that a soft constraint under a constraint if stays soft, as does the
// weighted choice of a dist.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin \
   $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

// if (sel) soft x == 1, against a hard constraint
class ClsSoft;
  rand bit [3:0] x;
  rand bit sel;
  constraint s {sel == 1;}
  constraint d {if (sel) soft x == 1;}
  constraint c {x > 10;}
endclass

// Only soft items in the then arm, only hard items in the else arm
class ClsSoftElse;
  rand bit [3:0] x;
  rand bit sel;
  constraint d {
    if (sel) {
      soft x == 1;
    } else {
      x == 12;
    }
  }
  constraint c {x > 10;}
endclass

// A hard and a soft item sharing one arm
class ClsHardSoft;
  rand bit [3:0] x;
  rand bit sel;
  constraint s {sel == 1;}
  constraint d {
    if (sel) {
      x == 2;
      soft x == 1;
    }
  }
endclass

// A nested if holding only a soft item, beside a hard item
class ClsNestedSoft;
  rand bit [3:0] x;
  rand bit sel;
  constraint s {sel == 1;}
  constraint d {
    if (sel) {
      if (x != 0) soft x == 1;
      x > 10;
    }
  }
endclass

// A nested if/else holding a soft and a hard arm
class ClsNestedElse;
  rand bit [3:0] x;
  rand bit sel;
  rand bit sel2;
  constraint s {sel == 1;}
  constraint d {
    if (sel) {
      if (sel2) {
        soft x == 1;
      } else {
        x == 12;
      }
    }
  }
  constraint c {x > 10;}
endclass

// A unique and a soft item sharing one arm
class ClsUniqueSoft;
  rand bit [3:0] a[3];
  rand bit sel;
  constraint s {sel == 1;}
  constraint d {
    if (sel) {
      unique {a};
      soft a[0] == a[1];
    }
  }
endclass

// A dist in both arms, the heavy bucket of the taken one excluded
class ClsDist;
  rand bit [3:0] x;
  rand bit sel;
  constraint s {sel == 1;}
  constraint d {
    if (sel) {
      x dist {
        [0 : 3] :/ 90,
        [12 : 15] :/ 10
      };
    } else {
      x dist {7 :/ 1};
    }
  }
  constraint c {x > 10;}
endclass

// A dist in the then arm, a hard item in the else arm
class ClsDistElse;
  rand bit [3:0] x;
  rand bit sel;
  constraint s {sel == 1;}
  constraint d {
    if (sel) {
      x dist {
        [0 : 3] :/ 90,
        [12 : 15] :/ 10
      };
    } else {
      x == 7;
    }
  }
  constraint c {x > 10;}
endclass

// A dist in an if with no else arm
class ClsDistNoElse;
  rand bit [3:0] x;
  rand bit sel;
  constraint s {sel == 1;}
  constraint d {
    if (sel) {
      x dist {
        [0 : 3] :/ 90,
        [12 : 15] :/ 10
      };
    }
  }
  constraint c {x > 10;}
endclass

// A dist in a foreach under an if/else
class ClsDistForeach;
  rand bit [3:0] a[3];
  rand bit sel;
  constraint s {sel == 1;}
  constraint d {
    if (sel) {
      foreach (a[i]) {
        a[i] dist {
          [0 : 3] :/ 90,
          [12 : 15] :/ 10
        };
      }
    } else {
      foreach (a[i]) {a[i] == 7;}
    }
  }
  constraint c {foreach (a[i]) {a[i] > 10;}}
endclass

// Soft items under an if with nothing opposing them, beside a conflicting one
class ClsSoftKept;
  rand bit [3:0] x;
  rand bit [3:0] y;
  rand bit [3:0] z;
  rand bit sel;
  constraint s {sel == 1;}
  constraint d {if (sel) soft x == 1;}
  constraint d2 {
    if (sel) {
      y == 3;
      soft z == 1;
    }
  }
  constraint c {x > 10;}
endclass

// A dist in a foreach under an if/else, the else arm free to be taken
class ClsDistForeachElse;
  rand bit [3:0] a[3];
  rand bit sel;
  constraint d {
    if (sel) {
      foreach (a[i]) {
        a[i] dist {
          [0 : 3] :/ 90,
          [12 : 15] :/ 10
        };
      }
    } else {
      foreach (a[i]) {a[i] == 7;}
    }
  }
endclass

module t;
  initial begin
    int randomize_result;
    // The hard constraint wins over a soft one under an if
    begin
      static ClsSoft obj = new();
      repeat (20) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        `checkd(obj.x > 10, 1'b1);
      end
    end

    // Each arm keeps its own softness
    begin
      static ClsSoftElse obj = new();
      repeat (20) begin
        randomize_result = obj.randomize() with {sel == 1'b1;};
        `checkd(randomize_result, 1);
        `checkd(obj.x > 10, 1'b1);
        randomize_result = obj.randomize() with {sel == 1'b0;};
        `checkd(randomize_result, 1);
        `checkd(obj.x, 12);
      end
    end

    // The hard item of an arm wins over the soft item beside it
    begin
      static ClsHardSoft obj = new();
      repeat (20) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        `checkd(obj.x, 2);
      end
    end

    // A soft item in a nested if yields to the hard item beside that if
    begin
      static ClsNestedSoft obj = new();
      repeat (20) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        `checkd(obj.x > 10, 1'b1);
      end
    end

    // Each arm of a nested if/else keeps its own softness
    begin
      static ClsNestedElse obj = new();
      repeat (20) begin
        randomize_result = obj.randomize() with {sel2 == 1'b1;};
        `checkd(randomize_result, 1);
        `checkd(obj.x > 10, 1'b1);
        randomize_result = obj.randomize() with {sel2 == 1'b0;};
        `checkd(randomize_result, 1);
        `checkd(obj.x, 12);
      end
    end

    // The unique of an arm wins over the soft item beside it
    begin
      static ClsUniqueSoft obj = new();
      repeat (20) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        `checkd(obj.a[0] != obj.a[1], 1'b1);
        `checkd(obj.a[0] != obj.a[2], 1'b1);
        `checkd(obj.a[1] != obj.a[2], 1'b1);
      end
    end

    // With the heavy bucket excluded, a dist under an if draws the other one
    begin
      static ClsDist obj = new();
      repeat (20) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        `checkd((obj.x inside {[12 : 15]}), 1'b1);
      end
    end

    // The same with a hard item in the else arm
    begin
      static ClsDistElse obj = new();
      repeat (20) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        `checkd((obj.x inside {[12 : 15]}), 1'b1);
      end
    end

    // The same with no else arm
    begin
      static ClsDistNoElse obj = new();
      repeat (20) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        `checkd((obj.x inside {[12 : 15]}), 1'b1);
      end
    end

    // The same for every element of a foreach under the if
    begin
      static ClsDistForeach obj = new();
      repeat (20) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        foreach (obj.a[i]) `checkd((obj.a[i] inside {[12 : 15]}), 1'b1);
      end
    end

    // A soft item under an if still applies when nothing opposes it
    begin
      static ClsSoftKept obj = new();
      repeat (20) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        `checkd(obj.x > 10, 1'b1);
        `checkd(obj.y, 3);
        `checkd(obj.z, 1);
      end
    end

    // The else arm of a foreach under an if/else
    begin
      static ClsDistForeachElse obj = new();
      repeat (20) begin
        randomize_result = obj.randomize() with {sel == 1'b0;};
        `checkd(randomize_result, 1);
        foreach (obj.a[i]) `checkd(obj.a[i], 7);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
