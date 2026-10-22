// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class external_cl;
  int x;
  int y;
  logic [7:0] dyn[][];

  function new();
    x = 0;
    y = 0;
    dyn = new[4];
    foreach (dyn[i]) dyn[i] = new[1];
  endfunction
endclass

module t;
  initial begin
    int a, b;
    automatic int limit = 10;
    external_cl obj;

    // Test 1: Basic std::randomize with 'with' clause
    if (std::randomize(
            a, b
        ) with {
          2 < a;
          a < 7;
          b < a;
        } != 1)
      $stop;
    if (!(2 < a && a < 7 && b < a)) $stop;
    $display("Test 1 passed: a=%0d, b=%0d", a, b);

    // Test 2: Local variable and class member with mutual constraints
    obj = new;
    if (std::randomize(
            a, obj.x
        ) with {
          a > 10;
          a < 20;
          obj.x > a;
          obj.x < a + 5;
        } != 1)
      $stop;
    if (!(a > 10 && a < 20 && obj.x > a && obj.x < a + 5)) $stop;
    $display("Test 2 passed: a=%0d, obj.x=%0d (obj.x between a+1 and a+4)", a, obj.x);

    // Test 3: Reference external variable in constraint
    if (std::randomize(
            a
        ) with {
          a > 0;
          a < limit;
        } != 1)
      $stop;
    if (!(a > 0 && a < limit)) $stop;
    $display("Test 3 passed: a=%0d, limit=%0d", a, limit);

    // Test 4: Randomize class member variables
    obj = new;
    if (std::randomize(
            obj.x, obj.y
        ) with {
          obj.x > 5;
          obj.x < 20;
          obj.y == obj.x + 1;
        } != 1)
      $stop;
    if (!(obj.x > 5 && obj.x < 20 && obj.y == obj.x + 1)) $stop;
    $display("Test 4 passed: obj.x=%0d, obj.y=%0d", obj.x, obj.y);

    // Test 5: Multiple class members and local variable
    if (std::randomize(
            a, obj.x, obj.y
        ) with {
          a > 0;
          a < 5;
          obj.x > a;
          obj.y > obj.x;
          obj.y < a + 10;
        } != 1)
      $stop;
    if (!(a > 0 && a < 5 && obj.x > a && obj.y > obj.x && obj.y < a + 10)) $stop;
    $display("Test 5 passed: a=%0d, obj.x=%0d, obj.y=%0d", a, obj.x, obj.y);

    // Test 6: Member of 2D array
    assert (std::randomize(obj.dyn[2][0]) with {obj.dyn[2][0] inside {[1 : 10]};} == 1);
    if (!(obj.dyn[2][0] inside {[1 : 10]})) $stop;
    $display("Test 6 passed: obj.dyn[2][0]=%0d", obj.dyn[2][0]);

    // Test 7: Unsatisfiable constraints leave every argument unchanged
    // (IEEE 1800-2023 18.6.3 and 18.12)
    begin
      bit [7:0] x;
      bit [7:0] y;
      bit [64:0] wide;
      bit [30:0] q[$];
      bit [14:0] arr[3:1];
      int randomize_result;
      x = 41;
      y = 42;
      wide = 65'h1_2345_6789_abcd_ef01;
      q = '{1, 2, 3};
      foreach (arr[i]) arr[i] = 15'(i * 3);
      randomize_result = std::randomize(x, y, wide, q, arr) with {
        x + y == 8'd10;
        x + y == 8'd11;
      };
      `checkd(randomize_result, 0);
      `checkd(x, 41);
      `checkd(y, 42);
      `checkh(wide, 65'h1_2345_6789_abcd_ef01);
      foreach (q[i]) `checkd(q[i], 31'(i + 1));
      foreach (arr[i]) `checkd(arr[i], 15'(i * 3));
      $display("Test 7 passed: x=%0d, y=%0d", x, y);
    end

    // Test 8: Arguments that repeat or overlap also keep their previous values
    begin
      bit [14:0] x;
      bit [14:0] arr[3];
      int randomize_result;
      x = 7;
      arr = '{1, 2, 3};
      randomize_result = std::randomize(x, x, arr, arr[1]) with {
        x > 10;
        x < 5;
      };
      `checkd(randomize_result, 0);
      `checkd(x, 7);
      foreach (arr[i]) `checkd(arr[i], 15'(i + 1));
      $display("Test 8 passed: x=%0d", x);
    end

    // Test 9: A size constraint that can be met, with contradictory element
    // constraints, leaves a dynamic array's size and elements unchanged
    begin
      int dyn[];
      int randomize_result;
      dyn = '{5, 6};
      randomize_result = std::randomize(dyn) with {
        dyn.size() == 3;
        foreach (dyn[i]) {
          dyn[i] == 1;
          dyn[i] == 2;
        }
      };
      `checkd(randomize_result, 0);
      `checkd(dyn.size(), 2);
      `checkd(dyn[0], 5);
      `checkd(dyn[1], 6);
      $display("Test 9 passed: dyn.size()=%0d", dyn.size());
    end

    // Test 10: The same for a queue
    begin
      int q[$];
      int randomize_result;
      q = '{7};
      randomize_result = std::randomize(q) with {
        q.size() == 4;
        foreach (q[i]) {
          q[i] > 5;
          q[i] < 3;
        }
      };
      `checkd(randomize_result, 0);
      `checkd(q.size(), 1);
      `checkd(q[0], 7);
      $display("Test 10 passed: q.size()=%0d", q.size());
    end

    // Test 11: No arguments, so there is nothing to restore
    begin
      int a;
      int randomize_result;
      a = 3;
      randomize_result = std::randomize() with {a > 2;};
      `checkd(randomize_result, 1);
      randomize_result = std::randomize() with {a > 5;};
      `checkd(randomize_result, 0);
      `checkd(a, 3);
      $display("Test 11 passed: a=%0d", a);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
