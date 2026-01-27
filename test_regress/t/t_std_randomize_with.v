// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class external_cl;
   int x;
   int y;

   function new();
      x = 0;
      y = 0;
   endfunction
endclass

module t;
   initial begin
      int a, b;
      int limit = 10;
      external_cl obj;

      // Test 1: Basic std::randomize with 'with' clause
      if (std::randomize(a, b) with { 2 < a; a < 7; b < a; } != 1) $stop;
      if (!(2 < a && a < 7 && b < a)) $stop;
      $display("Test 1 passed: a=%0d, b=%0d", a, b);

      // Test 2: Local variable and class member with mutual constraints
      obj = new;
      if (std::randomize(a, obj.x) with { a > 10; a < 20; obj.x > a; obj.x < a + 5; } != 1) $stop;
      if (!(a > 10 && a < 20 && obj.x > a && obj.x < a + 5)) $stop;
      $display("Test 2 passed: a=%0d, obj.x=%0d (obj.x between a+1 and a+4)", a, obj.x);

      // Test 3: Reference external variable in constraint
      if (std::randomize(a) with { a > 0; a < limit; } != 1) $stop;
      if (!(a > 0 && a < limit)) $stop;
      $display("Test 3 passed: a=%0d, limit=%0d", a, limit);

      // Test 4: Randomize class member variables
      obj = new;
      if (std::randomize(obj.x, obj.y) with { obj.x > 5; obj.x < 20; obj.y == obj.x + 1; } != 1) $stop;
      if (!(obj.x > 5 && obj.x < 20 && obj.y == obj.x + 1)) $stop;
      $display("Test 4 passed: obj.x=%0d, obj.y=%0d", obj.x, obj.y);

      // Test 5: Multiple class members and local variable
      if (std::randomize(a, obj.x, obj.y) with { a > 0; a < 5; obj.x > a; obj.y > obj.x; obj.y < a + 10; } != 1) $stop;
      if (!(a > 0 && a < 5 && obj.x > a && obj.y > obj.x && obj.y < a + 10)) $stop;
      $display("Test 5 passed: a=%0d, obj.x=%0d, obj.y=%0d", a, obj.x, obj.y);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
