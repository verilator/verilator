// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg [1:0] in;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [1:0]           out10;                  // From test of Test.v
   wire [1:0]           out32;                  // From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
              // Outputs
              .out32                    (out32[1:0]),
              .out10                    (out10[1:0]),
              // Inputs
              .in                       (in[1:0]));

   // Test loop
   always @ (posedge clk) begin
      in <= in + 1;
`ifdef TEST_VERBOSE
      $write("[%0t] in=%d out32=%d out10=%d\n", $time, in, out32, out10);
`endif
      if (in==3) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module Test (/*AUTOARG*/
   // Outputs
   out32, out10,
   // Inputs
   in
   );
   input  [1:0] in;
   output [1:0] out32;
   output [1:0] out10;

   assign out32 = in[3:2];
   assign out10 = in[1:0];
endmodule
