// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test 'disable soft' constraint support.
// When 'disable soft var' is specified, soft constraints on that variable
// should be ignored, allowing hard constraints to take effect.

class disable_soft_test;
   rand int value;

   // Soft constraint: value should be < 50
   constraint c_soft {
      soft value < 50;
   }

   // Hard constraint: value must be >= 100
   constraint c_hard {
      value >= 100;
      value < 200;
   }

   // Without 'disable soft', these constraints conflict (soft < 50 vs hard >= 100)
   // With 'disable soft value', the soft constraint is ignored

   function new();
      value = 0;
   endfunction
endclass

module t;
   disable_soft_test obj;
   int successes;

   initial begin
      obj = new();
      successes = 0;

      // Test with conflicting constraints - should still work because
      // randomize() with inline 'disable soft' should disable the soft constraint
      repeat(20) begin
         // Using randomize() with inline disable soft
         // verilator lint_off WIDTHTRUNC
         if (obj.randomize() with { disable soft value; }) begin
         // verilator lint_on WIDTHTRUNC
            // With disable soft, only hard constraint applies: 100 <= value < 200
            if (obj.value >= 100 && obj.value < 200) begin
               successes++;
            end else begin
               $display("ERROR: value=%0d out of range [100,200)", obj.value);
               $stop;
            end
         end else begin
            $display("ERROR: randomize() failed");
            $stop;
         end
      end

      if (successes != 20) begin
         $display("ERROR: Only %0d/20 randomizations succeeded", successes);
         $stop;
      end

      $display("All %0d randomizations produced values in [100,200)", successes);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
