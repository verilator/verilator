// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test: Static variable in task inside interface with timing control
// Issue: V3Fork's needsDynScope() was incorrectly capturing static variables
// into dynamic scope classes, causing "VarRef missing VarScope pointer" error
//
// This test verifies that such patterns compile without internal errors.

interface TestIface(input logic clk);
    logic output_signal = 0;

    // Task with static variable and timing/non-blocking assignments
    // This pattern is common in UVM VIPs (e.g., baud clock generators)
    task BaudClkGenerator(input int divisor);
        static int count = 0;  // Static variable - must not be captured in dynamic scope
        forever begin
            @(posedge clk)
            if (count == (divisor - 1)) begin
                count <= 0;  // Non-blocking assignment
                output_signal <= ~output_signal;
            end else begin
                count <= count + 1;
            end
        end
    endtask

    // Another task to verify multiple static variables work
    task AnotherTask();
        static int another_count = 0;
        @(posedge clk);
        another_count = another_count + 1;
    endtask
endinterface

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   TestIface u_iface(clk);

   initial begin
      fork
         u_iface.BaudClkGenerator(4);  // Call task with static variable
      join_none
   end
endmodule
