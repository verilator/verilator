// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test soft constraint support.
// Soft constraints should be satisfied when possible, but dropped when
// they conflict with hard constraints.

class soft_constraint_basic;
   rand bit [7:0] value;

   // Soft constraint: prefer value in range [10:20]
   constraint c_soft { soft value inside {[10:20]}; }

   function new();
      value = 0;
   endfunction
endclass

class soft_constraint_conflict;
   rand bit [7:0] value;

   // Hard constraint: value must be > 100
   constraint c_hard { value > 100; }

   // Soft constraint: prefer value < 50 (conflicts with hard!)
   constraint c_soft { soft value < 50; }

   function new();
      value = 0;
   endfunction

   function void check();
      // Hard constraint must always be satisfied
      if (!(value > 100)) begin
         $display("ERROR: Hard constraint violated! value=%0d should be > 100", value);
         $stop;
      end
   endfunction
endclass

class soft_constraint_multiple;
   rand bit [7:0] a;
   rand bit [7:0] b;

   // Hard constraint
   constraint c_hard { a + b == 100; }

   // Soft constraints that can be satisfied together with hard
   constraint c_soft1 { soft a > 30; }
   constraint c_soft2 { soft b > 30; }

   function new();
      a = 0;
      b = 0;
   endfunction

   function void check();
      // Hard constraint must always be satisfied
      if (a + b != 100) begin
         $display("ERROR: Hard constraint violated! a=%0d + b=%0d != 100", a, b);
         $stop;
      end
   endfunction
endclass

module t;
   soft_constraint_basic obj_basic;
   soft_constraint_conflict obj_conflict;
   soft_constraint_multiple obj_multiple;

   initial begin
      // Test basic soft constraint
      obj_basic = new();
      repeat(5) begin
         if (obj_basic.randomize() != 1) begin
            $display("ERROR: randomize() failed for basic");
            $stop;
         end
         // Soft constraint suggests [10:20], but any value is acceptable
         $display("Basic: value=%0d", obj_basic.value);
      end

      // Test soft constraint that conflicts with hard constraint
      // Randomization should succeed by dropping soft constraint
      obj_conflict = new();
      repeat(5) begin
         if (obj_conflict.randomize() != 1) begin
            $display("ERROR: randomize() failed for conflict case");
            $stop;
         end
         obj_conflict.check();
         $display("Conflict: value=%0d (must be > 100)", obj_conflict.value);
      end

      // Test multiple soft constraints
      obj_multiple = new();
      repeat(5) begin
         if (obj_multiple.randomize() != 1) begin
            $display("ERROR: randomize() failed for multiple");
            $stop;
         end
         obj_multiple.check();
         $display("Multiple: a=%0d, b=%0d (sum=%0d)", obj_multiple.a, obj_multiple.b,
                  obj_multiple.a + obj_multiple.b);
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
