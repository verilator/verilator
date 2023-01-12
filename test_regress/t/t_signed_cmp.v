// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   logic signed [2:0] a_signed;
   logic signed [2:0] b_signed;
   logic [2:0] a_unsigned;
   logic [2:0] b_unsigned;

   logic custom_signed_out;
   logic custom_unsigned_out;
   logic normal_signed_out;
   logic normal_unsigned_out;

   // Signed comparisons
   custom_cmp #(.element_type(logic signed [2:0])) custom_signed_cmp (.a(a_signed), .b(b_signed), .c(custom_signed_out));
   signed_cmp normal_signed_cmp (.a(a_signed), .b(b_signed), .c(normal_signed_out));

   // Unsigned comparisons
   custom_cmp #(.element_type(logic [2:0])) custom_unsigned_cmp (.a(a_unsigned), .b(b_unsigned), .c(custom_unsigned_out));
   unsigned_cmp normal_unsigned_cmp (.a(a_unsigned), .b(b_unsigned), .c(normal_unsigned_out));

   integer cyc; initial cyc = 0;
   initial a_signed = 3'b001;
   initial b_signed = 3'b111;
   initial a_unsigned = 3'b001;
   initial b_unsigned = 3'b111;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==2) begin
`ifdef TEST_VERBOSE
         $write("Signed comparisons:\n");
         $write("custom_signed_cmp %d < %d = %b\n", a_signed, b_signed, custom_signed_out);
         $write("normal_signed_cmp %d < %d = %b\n", a_signed, b_signed, normal_signed_out);
         $write("Unsigned comparisons:\n");
         $write("custom_unsigned_cmp %d < %d = %b\n", a_unsigned, b_unsigned, custom_unsigned_out);
         $write("normal_unsigned_cmp %d < %d = %b\n", a_unsigned, b_unsigned, normal_unsigned_out);
`endif
         if (custom_signed_out !== normal_signed_out) begin
            $display("%%Error: bad signed comparison %d < %d: got=%b exp=%b", a_signed, b_signed, custom_signed_out, normal_signed_out);
            $stop;
         end
         if (custom_unsigned_out !== normal_unsigned_out) begin
            $display("%%Error: bad unsigned comparison %d < %d: got=%b exp=%b", a_unsigned, b_unsigned, custom_unsigned_out, normal_unsigned_out);
            $stop;
         end
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule


module custom_cmp
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

module signed_cmp
(
   input logic signed [2:0] a,
   input logic signed [2:0] b,
   output logic c
);
   assign c = a < b;
endmodule

module unsigned_cmp
(
   input logic [2:0] a,
   input logic [2:0] b,
   output logic c
);
   assign c = a < b;
endmodule
