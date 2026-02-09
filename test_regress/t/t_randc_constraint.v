// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test: randc variables with additional constraints limiting values
// IEEE 1800 Section 18.4.2: randc cyclic behavior over constrained domain

class RandcRange;
   randc bit [3:0] value;  // 4-bit: unconstrained domain = 0-15

   constraint c_range {
      value >= 3;
      value <= 10;
   }

   function void test_cyclic;
      automatic int count[16];
      automatic int domain_size = 8;  // values 3..10
      automatic int randomize_result;
      $display("Test randc with range constraint [3:10]");
      // Run 3 full cycles
      for (int trial = 0; trial < 3; ++trial) begin
         for (int i = 0; i < domain_size; ++i) begin
            randomize_result = randomize();
            if (randomize_result !== 1) begin
               $display("%%Error: randomize() failed");
               $stop;
            end
            if (value < 3 || value > 10) begin
               $display("%%Error: value %0d out of constrained range [3:10]", value);
               $stop;
            end
`ifdef TEST_VERBOSE
            $display("  trial=%0d i=%0d value=%0d", trial, i, value);
`endif
            ++count[value];
         end
      end
      // After 3 full cycles, each value in [3,10] should appear exactly 3 times
      for (int v = 3; v <= 10; ++v) begin
         if (count[v] != 3) begin
            $display("%%Error: value %0d appeared %0d times, expected 3", v, count[v]);
            $stop;
         end
      end
      // Values outside [3,10] should never appear
      for (int v = 0; v < 3; ++v) begin
         if (count[v] != 0) begin
            $display("%%Error: value %0d appeared %0d times, expected 0", v, count[v]);
            $stop;
         end
      end
      for (int v = 11; v < 16; ++v) begin
         if (count[v] != 0) begin
            $display("%%Error: value %0d appeared %0d times, expected 0", v, count[v]);
            $stop;
         end
      end
   endfunction
endclass

class RandcSmall;
   randc bit [1:0] val;  // 4 possible values: 0,1,2,3
   constraint c_exclude { val != 0; }  // 3 valid values: 1,2,3

   function void test_cyclic;
      automatic int count[4];
      automatic int domain_size = 3;
      automatic int randomize_result;
      $display("Test randc with exclude constraint (val != 0)");
      // Run 4 full cycles
      for (int trial = 0; trial < 4; ++trial) begin
         for (int i = 0; i < domain_size; ++i) begin
            randomize_result = randomize();
            if (randomize_result !== 1) begin
               $display("%%Error: randomize() failed");
               $stop;
            end
            if (val == 0) begin
               $display("%%Error: val == 0 violates constraint");
               $stop;
            end
`ifdef TEST_VERBOSE
            $display("  trial=%0d i=%0d val=%0d", trial, i, val);
`endif
            ++count[val];
         end
      end
      // After 4 full cycles, each of 1,2,3 should appear exactly 4 times
      if (count[0] != 0) begin
         $display("%%Error: val 0 appeared %0d times, expected 0", count[0]);
         $stop;
      end
      for (int v = 1; v <= 3; ++v) begin
         if (count[v] != 4) begin
            $display("%%Error: val %0d appeared %0d times, expected 4", v, count[v]);
            $stop;
         end
      end
   endfunction
endclass

module t;
   RandcRange rr;
   RandcSmall rs;

   initial begin
      rr = new;
      rr.test_cyclic();

      rs = new;
      rs.test_cyclic();

      $write("*-* All Finished *-*\n");
      $finish();
   end
endmodule
