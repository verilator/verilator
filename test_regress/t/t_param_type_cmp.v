// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t ();

   logic [2:0] a;
   logic [2:0] b;

   logic signed_out;
   logic unsigned_out;

   cmp #(.element_type(logic signed [2:0])) signed_cmp (.a(a), .b(b), .c(signed_out));
   cmp #(.element_type(logic [2:0])) unsigned_cmp (.a(a), .b(b), .c(unsigned_out));

   initial a = 3'b001;
   initial b = 3'b111;

   initial begin
      #1;
      if (signed_out !== 1'b0) begin
         $display("%%Error: bad signed comparison %b < %b: got=%d exp=%d", a, b, signed_out, 1'b0);
         $stop;
      end
      if (unsigned_out !== 1'b1) begin
         $display("%%Error: bad unsigned comparison %b < %b: got=%d exp=%d", a, b, unsigned_out, 1'b1);
         $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module cmp
#(
    parameter type element_type = logic
)
(
   input element_type a,
   input element_type b,
   output logic c
);

   assign c = a < b;

endmodule
