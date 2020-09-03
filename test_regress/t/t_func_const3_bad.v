// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

module c9
   #(parameter A = 1,
     parameter B = 1);

   localparam BITS = A*B;
   localparam SOMEP = {BITS{1'b0}};

endmodule

module b9
   #(parameter A = 1);

   c9
   #(.A (A),
     .B (9))
   c9;

endmodule

module t;

   b9 b9;
   b9 #(.A (100)) b900;
   b9 #(.A (1000)) b9k;

   initial begin
      // Should never get here
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
