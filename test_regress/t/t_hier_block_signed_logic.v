// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2024 by Antmicro. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t(/*AUTOARG*/
   // inputs
   clk
);
   input clk;

   logic signed [31:0] in1 = 3;
   logic signed [31:0] in2 = 4;
   logic signed in_small1 = 1;
   logic signed in_small2 = -1;

   logic signed [31:0] out1;
   logic signed [31:0] out2;
   logic signed out_small1;
   logic signed out_small2;

   sub sub1(.in(in1), .in_small(in_small1), .out(out1), .out_small(out_small1));
   sub sub2(.in(in2), .in_small(in_small2), .out(out2), .out_small(out_small2));

   always_ff @(posedge clk) begin
      if (out1 == signed'(-3)
            && out2 == signed'(-4)
            && out_small1 == signed'(1'b1)
            && out_small2 == signed'(1'b1)) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $write("Mismatch\n");
         $stop;
      end
   end
endmodule

module sub(
   input logic signed [31:0] in,
   input logic signed in_small,
   output logic signed [31:0] out,
   output logic signed out_small
); /*verilator hier_block*/
   assign out = -in;
   assign out_small = -in_small;
endmodule
