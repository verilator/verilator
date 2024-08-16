// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


typedef struct packed {
    logic      field0;
    logic      field1;
} new_struct_t;

module t (/*AUTOARG*/
   // Inputs
   clk
);
   input clk;

    new_struct_t bar_in;
    new_struct_t bar_out;

    Foo foo(bar_in, bar_out);

    // Test procedure
    initial begin
      integer i;
      new_struct_t initOut;

      bar_in = '0;  // Set bar_in to 0 initially  

      // Wait for the first falling edge of the clock
      @(negedge clk);

      // Capture the initial output value
      initOut = bar_out;

      // Apply stimulus for 10 clock cycles
      for (i = 0; i < 10; i = i + 1) begin
        if (i > 0) begin
          bar_in = '1;  // Switch to 1 after the first cycle
        end

        @(negedge clk);

        // Check if the output field0 has changed
        $display("bar_out.field0 = %h", bar_out.field0);
        $display("initOut.field0 = %h", initOut.field0);
        if (bar_out.field0 !== initOut.field0) begin
          $display("ERROR: bar_out value changed when it should not have");
          $stop;
        end
      end

      $display("Test passed");
      $write("*-* All Finished *-*\n");
      $finish;
    end

endmodule

module Foo(
  input new_struct_t bar_in, 
  output new_struct_t bar_out
);
    // this is a continuous assignment
    always_comb begin 
        bar_out.field1 = bar_in.field1;
    end

    // this should be an initial assignment, but verilator thinks it's a continous assignment
    logic temp0 = bar_in.field0;
    // If it is observed (verilator public, coverage, etc.), then it switches correctly to initial
    // logic temp0 /* verilator public */  = bar_in.field0;

    always_comb begin 
        bar_out.field0 = temp0;
    end
endmodule

