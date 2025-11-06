// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Josse Van Delm.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off WIDTH

module m2 #(parameter int N = 4)
   (input [N-1:0] i0, i1,
    input s,
    output [N-1:0] y);

   assign y = s ? i1 : i0;
endmodule

module m4 #(parameter int N = 4)
   (input [N-1:0] i0, i1, i2, i3,
    input [1:0] S,
    output [N-1:0] y);

   wire [N-1:0] o_low, o_high;

   // See issue #4920 - use of m4 without parameter overrides
   // caused the other use of m4(#(6)) to irop the #(N) below
   m2 #(N) lowm( .i0(i0), .i1(i1), .s(S[0]), .y(o_low));
   m2 #(N) highm( .i0(i2), .i1(i3), .s(S[0]), .y(o_high));
   m2 #(N) finalm( .i0(o_low), .i1(o_high), .s(S[1]), .y(y));

endmodule

module m8 #(parameter int N = 4)
  (input [N-1:0] i0, i1, i2, i3, i4, i5, i6, i7,
   input [2:0] S,
   output [N-1:0] y);

   wire [N-1:0] o_low, o_high;

   m4 #(N) lowm(.i0(i0), .i1(i1), .i2(i2), .i3(i3), .S(S[1:0]), .y(o_low));
   m4 #(N) highm(.i0(i4), .i1(i5), .i2(i6), .i3(i7), .S(S[1:0]), .y(o_high));
   m2 #(N) finalm(.i0(o_low), .i1(o_high), .s(S[2]), .y(y));

endmodule

module t ();
   reg [5:0] i0, i1, i2, i3;
   reg [1:0] S;
   wire [5:0] Y;

   m4 #(6) iut(.i0(i0), .i1(i1), .i2(i2), .i3(i3), .S(S), .y(Y));

   initial begin
      i0 = 6'b000000; i1 = 6'b000001; i2 = 6'b000010; i3 = 6'b000100;
      S = 2'b00; #10;
      S = 2'b01; #10;
      $write("*-* All Finished *-*\n");
   end
endmodule
