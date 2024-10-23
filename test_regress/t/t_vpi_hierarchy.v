// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR

module t
  (
   // Declare some signals so we can see how I/O works
   input              clk,
   input              reset_l,

   output wire [1:0]  out_small,
   output wire [39:0] out_quad,
   output wire [69:0] out_wide,
   input [1:0]        in_small,
   input [39:0]       in_quad,
   input [69:0]       in_wide
   );

   // Connect up the outputs, using some trivial logic
   assign out_small = ~reset_l ? '0 : (in_small + 2'b1);
   assign out_quad  = ~reset_l ? '0 : (in_quad + 40'b1);
   assign out_wide  = ~reset_l ? '0 : (in_wide + 70'b1);

   // And an example sub module. The submodule will print stuff.
   sub sub (/*AUTOINST*/
            // Inputs
            .clk                        (clk),
            .reset_l                    (reset_l));

   // Print some stuff as an example
   initial begin
      $display("[%0t] Model running...\n", $time);
   end

endmodule

module sub
  (
   input clk /* verilator public_flat_rd */,
   input reset_l
   );

   // Example counter/flop
   reg [31:0] count_c;
   always_ff @ (posedge clk) begin
      if (!reset_l) begin
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         count_c <= 32'h0;
         // End of automatics
      end
      else begin
         count_c <= count_c + 1;
         if (count_c >= 3) begin
            // This write is a magic value the Makefile uses to make sure the
            // test completes successfully.
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

   // An example assertion
   always_ff @ (posedge clk) begin
      AssertionExample: assert (!reset_l || count_c<100);
   end

   // And example coverage analysis
   cover property (@(posedge clk) count_c==3);

endmodule
