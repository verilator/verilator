// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

function integer f_add(input [31:0] a, input [31:0] b);
   f_add = a+b;
   if (f_add == 15)
     $fatal(2, "f_add = 15");
endfunction

// Speced ok: function called from function
function integer f_add2(input [31:0] a, input [31:0] b, input [31:0] c);
   f_add2 = f_add(a,b)+c;
endfunction

module c9
   #(parameter A = 1,
     parameter B = 1);

   localparam SOMEP = f_add2(A, B, 9);

endmodule

module b8
   #(parameter A = 1);

   c9
   #(.A (A),
     .B (8))
   c9;

endmodule

module t;

   localparam P6 = f_add(5, 1);
   localparam P14 = f_add2(2, 3, f_add(4, 5));
   //localparam P24 = f_add2(7, 8, 9);

   b8 b8;
   b8 #(.A (6)) b8_a6;
   b8 #(.A (7)) b8_a7;

   initial begin
      // Should never get here
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
