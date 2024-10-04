// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Issue #5380

typedef struct packed {
    logic      field0;
    logic      field1;
} str_t;

module t (/*AUTOARG*/
   // Inputs
   clk
);
   input clk;

   str_t bar_in;
   str_t bar_out;

   Sub sub(bar_in, bar_out);

   // Test procedure
   initial begin
      integer i;
      str_t initOut;

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
            $display("%%Error: bar_out value changed when it should not have");
            $stop;
         end
      end

      $write("*-* All Finished *-*\n");
      $finish;
    end

endmodule

module Sub
  (
   input str_t bar_in,
   output str_t bar_out
   );

   // This is a continuous assignment
   always_comb begin
      bar_out.field1 = bar_in.field1;
   end

   // This should be an initial assignment, but verilator thinks it's a continous assignment
   logic temp0 = bar_in.field0;
   // If it is observed (verilator public, coverage, etc.), then it switches correctly to initial
   // logic temp0 /* verilator public */  = bar_in.field0;

   always_comb begin
      bar_out.field0 = temp0;
   end
endmodule
