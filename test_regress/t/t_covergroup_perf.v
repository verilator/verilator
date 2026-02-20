// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Performance test for functional coverage - measures sample() overhead

module t;
   logic [7:0] data;
   logic [3:0] state;
   logic [15:0] addr;

   // Large covergroup with multiple coverpoints and many bins
   covergroup cg_perf;
      // Coverpoint with many bins
      cp_data: coverpoint data {
         bins d0  = {0};
         bins d1  = {1};
         bins d2  = {2};
         bins d3  = {3};
         bins d4  = {4};
         bins d5  = {5};
         bins d6  = {6};
         bins d7  = {7};
         bins d8  = {8};
         bins d9  = {9};
         bins d10 = {[10:19]};
         bins d20 = {[20:29]};
         bins d30 = {[30:39]};
         bins d40 = {[40:49]};
         bins d50 = {[50:59]};
         bins rest = {[60:255]};
      }

      cp_state: coverpoint state {
         bins s0 = {0};
         bins s1 = {1};
         bins s2 = {2};
         bins s3 = {3};
         bins s4 = {4};
         bins s5 = {5};
         bins s6 = {6};
         bins s7 = {7};
         bins s8 = {8};
         bins s9 = {9};
         bins s10 = {10};
         bins s11 = {11};
         bins s12 = {12};
         bins s13 = {13};
         bins s14 = {14};
         bins s15 = {15};
      }

      // verilator lint_off UNSIGNED
      // verilator lint_off CMPCONST
      cp_addr: coverpoint addr {
         bins low    = {[16'h0000:16'h03FF]};  // [0:1023]
         bins mid    = {[16'h0400:16'h07FF]};  // [1024:2047]
         bins high   = {[16'h0800:16'hFFFF]};  // [2048:65535]
      }
      // verilator lint_on CMPCONST
      // verilator lint_on UNSIGNED

      // Cross coverage adds more bins
      cross_data_state: cross cp_data, cp_state;
   endgroup

   cg_perf cg_inst = new;

   initial begin
      automatic longint start_time, end_time, elapsed;
      automatic int iterations = 100000;
      automatic real avg_time_ns;

      $display("=== Functional Coverage Performance Test ===");
      $display("Iterations: %0d", iterations);

      // Measure sample() overhead
      start_time = $time;

      for (int i = 0; i < iterations; i++) begin
         // Vary the data to hit different bins
         data = i[7:0];
         state = i[3:0];
         addr = i[15:0];

         cg_inst.sample();
      end

      end_time = $time;
      elapsed = end_time - start_time;

      avg_time_ns = real'(elapsed) / real'(iterations);

      $display("Total time: %0d time units", elapsed);
      $display("Average time per sample(): %0.2f time units", avg_time_ns);
      $display("Coverage: %0.1f%%", cg_inst.get_inst_coverage());

      // Performance target: < 100 cycles per sample()
      // Assuming 1 time unit = 1 ns, typical CPU @ 3 GHz = 0.33 ns/cycle
      // 100 cycles = 33 ns
      if (avg_time_ns < 33.0) begin
         $display("PASS: Performance within target (< 100 cycles)");
      end else begin
         $display("WARNING: Performance may need optimization (> 100 cycles)");
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
