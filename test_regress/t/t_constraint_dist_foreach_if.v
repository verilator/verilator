// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// Test that dist constraints nested inside if / -> inside foreach produce
// values only within the declared distribution and cover all buckets.
//
// The bucket draw must also be made PER ELEMENT, not once per solve and then
// shared by every element. Counting buckets across all solves cannot tell those
// apart: a single hoisted draw still hits both buckets over 100 solves, it just
// never mixes them inside one solve. So each block also counts solves in which
// at least one element landed in each bucket. With dist {0 := 3, [1:4] := 1}
// over 4 elements a per-element draw mixes in about 86 of 100 solves, whereas a
// hoisted draw can never mix and gives exactly 0.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_mixed(what,gotv) do if ((gotv) == 0) begin $write("%%Error: %s:%0d: dist inside foreach+%s: bucket draw is not per-element, no solve mixed buckets\n", `__FILE__,`__LINE__, what); `stop; end while(0);
// verilog_format: on

// foreach (a[i]) if (gate) a[i] dist {...}
class ClsIf;
  rand bit [3:0] a[4];
  bit gate;
  constraint c {
    foreach (a[i]) {
      if (gate == 1'b1) {
        a[i] dist {
          4'd0 := 3,
          [4'd1 : 4'd4] := 1
        };
      }
    }
  }
endclass

// foreach (a[i]) gate -> a[i] dist {...}
class ClsImpl;
  rand bit [3:0] a[4];
  bit gate;
  constraint c {
    foreach (a[i]) {
      gate ->
      (a[i] dist {
        4'd0 := 3,
        [4'd1 : 4'd4] := 1
      });
    }
  }
endclass

// foreach (a[i]) gateA -> (gateB -> a[i] dist {...})  -- doubly-nested implication
class ClsImplChained;
  rand bit [3:0] a[4];
  bit gateA, gateB;
  constraint c {
    foreach (a[i]) {
      gateA ->
      (gateB -> (a[i] dist {
        4'd0 := 3,
        [4'd1 : 4'd4] := 1
      }));
    }
  }
endclass

module t;
  initial begin
    // Test if form
    begin
      static ClsIf obj = new();
      int seen_zero, seen_nonzero;
      int this_zero, this_nonzero, mixed;
      int randomize_result;
      obj.gate = 1'b1;
      seen_zero = 0;
      seen_nonzero = 0;
      mixed = 0;
      repeat (100) begin
        this_zero = 0;
        this_nonzero = 0;
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        foreach (obj.a[i]) begin
          if (obj.a[i] > 4) begin
            $write("%%Error: %s:%0d: if: value out of dist range: %0d\n", `__FILE__, `__LINE__,
                   obj.a[i]);
            $stop;
          end
          if (obj.a[i] == 0) begin
            seen_zero++;
            this_zero++;
          end
          else begin
            seen_nonzero++;
            this_nonzero++;
          end
        end
        if (this_zero > 0 && this_nonzero > 0) mixed++;
      end
      if (seen_zero == 0 || seen_nonzero == 0) begin
        $write(
            "%%Error: %s:%0d: dist inside foreach+if: not all buckets hit (zero=%0d nonzero=%0d)\n",
            `__FILE__, `__LINE__, seen_zero, seen_nonzero);
        $stop;
      end
      `check_mixed("if", mixed)
    end

    // Test -> (implication) form
    begin
      static ClsImpl obj = new();
      int seen_zero, seen_nonzero;
      int this_zero, this_nonzero, mixed;
      int randomize_result;
      obj.gate = 1'b1;
      seen_zero = 0;
      seen_nonzero = 0;
      mixed = 0;
      repeat (100) begin
        this_zero = 0;
        this_nonzero = 0;
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        foreach (obj.a[i]) begin
          if (obj.a[i] > 4) begin
            $write("%%Error: %s:%0d: ->: value out of dist range: %0d\n", `__FILE__, `__LINE__,
                   obj.a[i]);
            $stop;
          end
          if (obj.a[i] == 0) begin
            seen_zero++;
            this_zero++;
          end
          else begin
            seen_nonzero++;
            this_nonzero++;
          end
        end
        if (this_zero > 0 && this_nonzero > 0) mixed++;
      end
      if (seen_zero == 0 || seen_nonzero == 0) begin
        $write(
            "%%Error: %s:%0d: dist inside foreach+->: not all buckets hit (zero=%0d nonzero=%0d)\n",
            `__FILE__, `__LINE__, seen_zero, seen_nonzero);
        $stop;
      end
      `check_mixed("->", mixed)
    end

    // Test doubly-nested -> (chained implication) form
    begin
      static ClsImplChained obj = new();
      int seen_zero, seen_nonzero;
      int this_zero, this_nonzero, mixed;
      int randomize_result;
      obj.gateA = 1'b1;
      obj.gateB = 1'b1;
      seen_zero = 0;
      seen_nonzero = 0;
      mixed = 0;
      repeat (100) begin
        this_zero = 0;
        this_nonzero = 0;
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        foreach (obj.a[i]) begin
          if (obj.a[i] > 4) begin
            $write("%%Error: %s:%0d: ->->: value out of dist range: %0d\n", `__FILE__, `__LINE__,
                   obj.a[i]);
            $stop;
          end
          if (obj.a[i] == 0) begin
            seen_zero++;
            this_zero++;
          end
          else begin
            seen_nonzero++;
            this_nonzero++;
          end
        end
        if (this_zero > 0 && this_nonzero > 0) mixed++;
      end
      if (seen_zero == 0 || seen_nonzero == 0) begin
        $write(
            "%%Error: %s:%0d: dist inside foreach+->->: not all buckets hit (zero=%0d nonzero=%0d)\n",
            `__FILE__, `__LINE__, seen_zero, seen_nonzero);
        $stop;
      end
      `check_mixed("->->", mixed)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
