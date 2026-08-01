// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// Test that a dist constraint inside a foreach nested within a constraint if
// produces values only within the declared distribution, covers all buckets,
// honors the declared weights, and draws a bucket per array element.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin \
   $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkgt(gotv,minv) do if (!((gotv) > (minv))) begin \
   $write("%%Error: %s:%0d:  got=%0d expected > %0d\n", `__FILE__, `__LINE__, (gotv), (minv)); `stop; end while(0)
// verilog_format: on

// if (gate) foreach (a[i]) a[i] dist {...}
class ClsIf;
  rand bit [3:0] a[4];
  bit gate;
  constraint c {
    if (gate == 1'b1) {
      foreach (a[i]) {
        a[i] dist {
          4'd0 := 3,
          [4'd1 : 4'd4] := 1
        };
      }
    }
  }
endclass

// if (gate) foreach (a[i]) a[i] dist {...} else foreach (a[i]) a[i] dist {...}
class ClsIfElse;
  rand bit [3:0] a[4];
  bit gate;
  constraint c {
    if (gate == 1'b1) {
      foreach (a[i]) {
        a[i] dist {
          4'd0 := 3,
          [4'd1 : 4'd4] := 1
        };
      }
    } else {
      foreach (a[i]) {a[i] dist {[4'd8 : 4'd11] := 1};}
    }
  }
endclass

// if (gate) foreach (a[i]) gate2 -> a[i] dist {...}
class ClsIfImpl;
  rand bit [3:0] a[4];
  bit gate, gate2;
  constraint c {
    if (gate == 1'b1) {
      foreach (a[i]) {
        gate2 ->
        (a[i] dist {
          4'd0 := 3,
          [4'd1 : 4'd4] := 1
        });
      }
    }
  }
endclass

// if (sel) foreach (a[i]) a[i] dist {...}, with a randomized condition
class ClsRandSel;
  rand bit [2:0] a[4];
  rand bit sel;
  constraint c {
    if (sel) {
      foreach (a[i]) {
        a[i] dist {
          [3'd0 : 3'd1] :/ 90,
          [3'd2 : 3'd5] :/ 10
        };
      }
    }
  }
endclass

// Two dist constraints sharing one foreach body inside a constraint if
class ClsMulti;
  rand bit [2:0] a[4];
  rand bit [2:0] b[4];
  bit gate;
  constraint c {
    if (gate == 1'b1) {
      foreach (a[i]) {
        a[i] dist {
          [3'd0 : 3'd1] :/ 90,
          [3'd2 : 3'd5] :/ 10
        };
        b[i] dist {3'd7 := 1};
      }
    }
  }
endclass

// if (gate) foreach (m[i]) foreach (m[i][j]) m[i][j] dist {...}
class ClsNested;
  rand bit [2:0] m[2][2];
  bit gate;
  constraint c {
    if (gate == 1'b1) {
      foreach (m[i]) {
        foreach (m[i][j]) {
          m[i][j] dist {
            [3'd0 : 3'd1] :/ 90,
            [3'd2 : 3'd5] :/ 10
          };
        }
      }
    }
  }
endclass

// Two equally weighted, non-adjacent buckets, so a per-element bucket draw is
// observable as differing elements within a single randomize() call
class ClsIndep;
  rand bit [3:0] a[8];
  bit gate;
  constraint c {
    if (gate == 1'b1) {
      foreach (a[i]) {
        a[i] dist {
          4'd0 := 1,
          4'd9 := 1
        };
      }
    }
  }
endclass

// if (gate) foreach (q[i]) q[i] dist {...}, over a queue
class ClsQueue;
  rand bit [2:0] q[$];
  bit gate;
  constraint sz {q.size() == 4;}
  constraint c {
    if (gate == 1'b1) {
      foreach (q[i]) {
        q[i] dist {
          [3'd0 : 3'd1] :/ 90,
          [3'd2 : 3'd5] :/ 10
        };
      }
    }
  }
endclass

// if (gate) foreach (d[i]) d[i] dist {...}, over a dynamic array
class ClsDynArray;
  rand bit [2:0] d[];
  bit gate;
  constraint sz {d.size() == 4;}
  constraint c {
    if (gate == 1'b1) {
      foreach (d[i]) {
        d[i] dist {
          [3'd0 : 3'd1] :/ 90,
          [3'd2 : 3'd5] :/ 10
        };
      }
    }
  }
endclass

// Weight given by a variable rather than a literal
class ClsVarWeight;
  rand bit [2:0] a[4];
  bit gate;
  int w;
  constraint c {
    if (gate == 1'b1) {
      foreach (a[i]) {
        a[i] dist {
          [3'd0 : 3'd1] :/ w,
          [3'd2 : 3'd5] :/ 1
        };
      }
    }
  }
endclass

// foreach (m[i]) if (gate) foreach (m[i][j]) m[i][j] dist {...}, so the
// constraint if sits between the two foreach levels
class ClsForeachIfForeach;
  rand bit [2:0] m[2][4];
  bit gate;
  constraint c {
    foreach (m[i]) {
      if (gate == 1'b1) {
        foreach (m[i][j]) {
          m[i][j] dist {
            [3'd0 : 3'd1] :/ 90,
            [3'd2 : 3'd5] :/ 10
          };
        }
      }
    }
  }
endclass

// if (gate) foreach (a[i]) if (gate2) a[i] dist {...}
class ClsIfForeachIf;
  rand bit [2:0] a[4];
  bit gate, gate2;
  constraint c {
    if (gate == 1'b1) {
      foreach (a[i]) {
        if (gate2 == 1'b1) {
          a[i] dist {
            [3'd0 : 3'd1] :/ 90,
            [3'd2 : 3'd5] :/ 10
          };
        }
      }
    }
  }
endclass

module t;
  initial begin
    // dist inside if + foreach stays in range and reaches both buckets
    begin
      static ClsIf obj = new();
      int seen_zero, seen_nonzero;
      obj.gate = 1'b1;
      seen_zero = 0;
      seen_nonzero = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1);
        foreach (obj.a[i]) begin
          `checkd((obj.a[i] inside {[4'd0 : 4'd4]}), 1'b1);
          if (obj.a[i] == 0) seen_zero++;
          else seen_nonzero++;
        end
      end
      `checkgt(seen_zero, 0);
      `checkgt(seen_nonzero, 0);
    end

    // Each arm of an if/else selects its own distribution
    begin
      static ClsIfElse obj = new();
      int seen_zero, seen_nonzero, seen_else;
      obj.gate = 1'b1;
      seen_zero = 0;
      seen_nonzero = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1);
        foreach (obj.a[i]) begin
          `checkd((obj.a[i] inside {[4'd0 : 4'd4]}), 1'b1);
          if (obj.a[i] == 0) seen_zero++;
          else seen_nonzero++;
        end
      end
      `checkgt(seen_zero, 0);
      `checkgt(seen_nonzero, 0);
      obj.gate = 1'b0;
      seen_else = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1);
        foreach (obj.a[i]) begin
          `checkd((obj.a[i] inside {[4'd8 : 4'd11]}), 1'b1);
          seen_else++;
        end
      end
      `checkd(seen_else, 400);
    end

    // dist under an implication nested inside the if + foreach
    begin
      static ClsIfImpl obj = new();
      int seen_zero, seen_nonzero;
      obj.gate = 1'b1;
      obj.gate2 = 1'b1;
      seen_zero = 0;
      seen_nonzero = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1);
        foreach (obj.a[i]) begin
          `checkd((obj.a[i] inside {[4'd0 : 4'd4]}), 1'b1);
          if (obj.a[i] == 0) seen_zero++;
          else seen_nonzero++;
        end
      end
      `checkgt(seen_zero, 0);
      `checkgt(seen_nonzero, 0);
    end

    // A rand if condition applies the dist to every element when taken, and the
    // 90 :/ 10 weights make the low bucket dominate
    begin
      static ClsRandSel obj = new();
      int seen_low, seen_high;
      seen_low = 0;
      seen_high = 0;
      repeat (100) begin
        `checkd(obj.randomize() with {sel == 1'b1;}, 1);
        `checkd(obj.sel, 1'b1);
        foreach (obj.a[i]) begin
          `checkd((obj.a[i] inside {[3'd0 : 3'd5]}), 1'b1);
          if (obj.a[i] <= 1) seen_low++;
          else seen_high++;
        end
      end
      `checkgt(seen_low, 0);
      `checkgt(seen_high, 0);
      `checkgt(seen_low, seen_high);
    end

    // Two dist constraints in one foreach body are both honored
    begin
      static ClsMulti obj = new();
      int seen_low, seen_high;
      obj.gate = 1'b1;
      seen_low = 0;
      seen_high = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1);
        foreach (obj.a[i]) begin
          `checkd((obj.a[i] inside {[3'd0 : 3'd5]}), 1'b1);
          `checkd(obj.b[i], 3'd7);
          if (obj.a[i] <= 1) seen_low++;
          else seen_high++;
        end
      end
      `checkgt(seen_low, 0);
      `checkgt(seen_high, 0);
      `checkgt(seen_low, seen_high);
    end

    // A dist in a nested foreach under a constraint if
    begin
      static ClsNested obj = new();
      int seen_low, seen_high;
      obj.gate = 1'b1;
      seen_low = 0;
      seen_high = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1);
        foreach (obj.m[i]) begin
          foreach (obj.m[i][j]) begin
            `checkd((obj.m[i][j] inside {[3'd0 : 3'd5]}), 1'b1);
            if (obj.m[i][j] <= 1) seen_low++;
            else seen_high++;
          end
        end
      end
      `checkgt(seen_low, 0);
      `checkgt(seen_high, 0);
      `checkgt(seen_low, seen_high);
    end

    // The bucket is drawn per element, so one randomize() call can place
    // different elements in different buckets
    begin
      static ClsIndep obj = new();
      int seen_mixed;
      obj.gate = 1'b1;
      seen_mixed = 0;
      repeat (100) begin
        int seen_lo, seen_hi;
        `checkd(obj.randomize(), 1);
        seen_lo = 0;
        seen_hi = 0;
        foreach (obj.a[i]) begin
          `checkd((obj.a[i] inside {4'd0, 4'd9}), 1'b1);
          if (obj.a[i] == 4'd0) seen_lo++;
          else seen_hi++;
        end
        if (seen_lo > 0 && seen_hi > 0) seen_mixed++;
      end
      `checkgt(seen_mixed, 0);
    end

    // dist applies to every element of a queue
    begin
      static ClsQueue obj = new();
      int seen_low, seen_high;
      obj.gate = 1'b1;
      seen_low = 0;
      seen_high = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1);
        `checkd(obj.q.size(), 4);
        foreach (obj.q[i]) begin
          `checkd((obj.q[i] inside {[3'd0 : 3'd5]}), 1'b1);
          if (obj.q[i] <= 1) seen_low++;
          else seen_high++;
        end
      end
      `checkgt(seen_low, 0);
      `checkgt(seen_high, 0);
      `checkgt(seen_low, seen_high);
    end

    // dist applies to every element of a dynamic array
    begin
      static ClsDynArray obj = new();
      int seen_low, seen_high;
      obj.gate = 1'b1;
      seen_low = 0;
      seen_high = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1);
        `checkd(obj.d.size(), 4);
        foreach (obj.d[i]) begin
          `checkd((obj.d[i] inside {[3'd0 : 3'd5]}), 1'b1);
          if (obj.d[i] <= 1) seen_low++;
          else seen_high++;
        end
      end
      `checkgt(seen_low, 0);
      `checkgt(seen_high, 0);
      `checkgt(seen_low, seen_high);
    end

    // A weight held in a variable is read at run time, so a 3 :/ 1 split
    // reaches both buckets and leaves the low one dominant
    begin
      static ClsVarWeight obj = new();
      int seen_low, seen_high;
      obj.gate = 1'b1;
      obj.w = 3;
      seen_low = 0;
      seen_high = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1);
        foreach (obj.a[i]) begin
          `checkd((obj.a[i] inside {[3'd0 : 3'd5]}), 1'b1);
          if (obj.a[i] <= 1) seen_low++;
          else seen_high++;
        end
      end
      `checkgt(seen_low, 0);
      `checkgt(seen_high, 0);
      `checkgt(seen_low, seen_high);
    end

    // A constraint if between two foreach levels
    begin
      static ClsForeachIfForeach obj = new();
      int seen_low, seen_high;
      obj.gate = 1'b1;
      seen_low = 0;
      seen_high = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1);
        foreach (obj.m[i]) begin
          foreach (obj.m[i][j]) begin
            `checkd((obj.m[i][j] inside {[3'd0 : 3'd5]}), 1'b1);
            if (obj.m[i][j] <= 1) seen_low++;
            else seen_high++;
          end
        end
      end
      `checkgt(seen_low, 0);
      `checkgt(seen_high, 0);
      `checkgt(seen_low, seen_high);
    end

    // A second constraint if inside the foreach body
    begin
      static ClsIfForeachIf obj = new();
      int seen_low, seen_high;
      obj.gate = 1'b1;
      obj.gate2 = 1'b1;
      seen_low = 0;
      seen_high = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1);
        foreach (obj.a[i]) begin
          `checkd((obj.a[i] inside {[3'd0 : 3'd5]}), 1'b1);
          if (obj.a[i] <= 1) seen_low++;
          else seen_high++;
        end
      end
      `checkgt(seen_low, 0);
      `checkgt(seen_high, 0);
      `checkgt(seen_low, seen_high);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
