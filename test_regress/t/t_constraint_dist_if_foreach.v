// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// Test that a dist constraint inside a foreach nested within a constraint if
// produces values only within the declared distribution and covers all buckets.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
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

module t;
  initial begin
    // Test if form
    begin
      static ClsIf obj = new();
      int seen_zero, seen_nonzero;
      obj.gate = 1'b1;
      seen_zero = 0;
      seen_nonzero = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1)
        foreach (obj.a[i]) begin
          if (obj.a[i] > 4) begin
            $write("%%Error: %s:%0d: if: value out of dist range: %0d\n", `__FILE__, `__LINE__,
                   obj.a[i]);
            $stop;
          end
          if (obj.a[i] == 0) seen_zero++;
          else seen_nonzero++;
        end
      end
      if (seen_zero == 0 || seen_nonzero == 0) begin
        $write(
            "%%Error: %s:%0d: dist inside if+foreach: not all buckets hit (zero=%0d nonzero=%0d)\n",
            `__FILE__, `__LINE__, seen_zero, seen_nonzero);
        $stop;
      end
    end

    // Test if/else form, taking each arm in turn
    begin
      static ClsIfElse obj = new();
      int seen_zero, seen_nonzero, seen_else;
      obj.gate = 1'b1;
      seen_zero = 0;
      seen_nonzero = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1)
        foreach (obj.a[i]) begin
          if (obj.a[i] > 4) begin
            $write("%%Error: %s:%0d: if/else then: value out of dist range: %0d\n", `__FILE__,
                   `__LINE__, obj.a[i]);
            $stop;
          end
          if (obj.a[i] == 0) seen_zero++;
          else seen_nonzero++;
        end
      end
      if (seen_zero == 0 || seen_nonzero == 0) begin
        $write("%%Error: %s:%0d: dist inside if+foreach then arm: not all buckets hit ", `__FILE__,
               `__LINE__);
        $write("(zero=%0d nonzero=%0d)\n", seen_zero, seen_nonzero);
        $stop;
      end
      obj.gate = 1'b0;
      seen_else = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1)
        foreach (obj.a[i]) begin
          if (obj.a[i] < 8 || obj.a[i] > 11) begin
            $write("%%Error: %s:%0d: if/else else: value out of dist range: %0d\n", `__FILE__,
                   `__LINE__, obj.a[i]);
            $stop;
          end
          seen_else++;
        end
      end
      `checkd(seen_else, 400)
    end

    // Test implication nested inside the if+foreach
    begin
      static ClsIfImpl obj = new();
      int seen_zero, seen_nonzero;
      obj.gate = 1'b1;
      obj.gate2 = 1'b1;
      seen_zero = 0;
      seen_nonzero = 0;
      repeat (100) begin
        `checkd(obj.randomize(), 1)
        foreach (obj.a[i]) begin
          if (obj.a[i] > 4) begin
            $write("%%Error: %s:%0d: if+foreach+->: value out of dist range: %0d\n", `__FILE__,
                   `__LINE__, obj.a[i]);
            $stop;
          end
          if (obj.a[i] == 0) seen_zero++;
          else seen_nonzero++;
        end
      end
      if (seen_zero == 0 || seen_nonzero == 0) begin
        $write("%%Error: %s:%0d: dist inside if+foreach+->: not all buckets hit ", `__FILE__,
               `__LINE__);
        $write("(zero=%0d nonzero=%0d)\n", seen_zero, seen_nonzero);
        $stop;
      end
    end

    // Test rand if condition, dist applies to every element when the condition is taken
    begin
      static ClsRandSel obj = new();
      int seen_low, seen_high;
      seen_low = 0;
      seen_high = 0;
      repeat (100) begin
        `checkd(obj.randomize() with {sel == 1'b1;}, 1)
        `checkd(obj.sel, 1'b1)
        foreach (obj.a[i]) begin
          if (obj.a[i] > 5) begin
            $write("%%Error: %s:%0d: rand sel: value out of dist range: %0d\n", `__FILE__,
                   `__LINE__, obj.a[i]);
            $stop;
          end
          if (obj.a[i] <= 1) seen_low++;
          else seen_high++;
        end
      end
      if (seen_low == 0 || seen_high == 0) begin
        $write("%%Error: %s:%0d: dist inside if+foreach with rand cond: not all buckets hit ",
               `__FILE__, `__LINE__);
        $write("(low=%0d high=%0d)\n", seen_low, seen_high);
        $stop;
      end
      // Weights are 90 :/ 10, so the low bucket must dominate
      if (seen_low <= seen_high) begin
        $write("%%Error: %s:%0d: dist weights not honored (low=%0d high=%0d)\n", `__FILE__,
               `__LINE__, seen_low, seen_high);
        $stop;
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
