// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test distribution constraint support.
// The 'dist' constraint specifies weighted random selection among ranges.

class dist_test;
   rand int value;

   // Distribution constraint: value should be in one of the ranges
   // with weighted probability
   constraint c_dist {
      value dist { [0:10] := 1, [100:110] := 3 };
   }

   function new();
      value = 0;
   endfunction
endclass

module t;
   dist_test obj;
   int low_count;
   int high_count;

   initial begin
      obj = new();
      low_count = 0;
      high_count = 0;

      // Run many iterations to verify distribution
      repeat(100) begin
         // verilator lint_off WIDTHTRUNC
         if (obj.randomize()) begin
         // verilator lint_on WIDTHTRUNC
            // Check value is in valid range
            if (obj.value >= 0 && obj.value <= 10) begin
               low_count++;
            end else if (obj.value >= 100 && obj.value <= 110) begin
               high_count++;
            end else begin
               $display("ERROR: value=%0d out of valid ranges", obj.value);
               $stop;
            end
         end else begin
            $display("ERROR: randomize() failed");
            $stop;
         end
      end

      // With weights 1:3, we expect roughly 25% low, 75% high
      // But with random sampling, allow wide margin
      $display("Distribution: low_count=%0d, high_count=%0d", low_count, high_count);

      if (low_count + high_count != 100) begin
         $display("ERROR: Total count mismatch");
         $stop;
      end

      // Just verify both ranges were hit at least once
      if (low_count == 0) begin
         $display("ERROR: Low range [0:10] was never selected");
         $stop;
      end
      if (high_count == 0) begin
         $display("ERROR: High range [100:110] was never selected");
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
