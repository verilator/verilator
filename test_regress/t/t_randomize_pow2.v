// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that 2**n expressions work in constraints.
// SMT solvers don't support power operator directly, but 2**n can be
// transformed to 1<<n which is supported via bvshl.

class pow2_constraint_test;
   rand bit [7:0] n;
   rand bit [15:0] pow2_val;

   // Constraint using 2**n - this should be transformed to 1<<n internally
   constraint c_pow2 {
      n inside {[0:7]};
      pow2_val == 2**n;
   }

   function new();
      n = 0;
      pow2_val = 1;
   endfunction

   function void check();
      // Verify pow2_val is actually 2**n
      if (pow2_val != (16'h1 << n)) begin
         $display("ERROR: pow2_val=%0d but expected 2**%0d=%0d", pow2_val, n, 16'h1 << n);
         $stop;
      end
   endfunction
endclass

module t;
   pow2_constraint_test obj;

   initial begin
      obj = new();

      // Test multiple randomizations
      repeat(10) begin
         if (obj.randomize() != 1) begin
            $display("ERROR: randomize() failed");
            $stop;
         end
         obj.check();
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
