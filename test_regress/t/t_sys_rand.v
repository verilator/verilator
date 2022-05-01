// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   reg [31:0] lastrand;
   reg [31:0] thisrand;

   integer    same = 0;
   integer    i;

`define TRIES 20

   initial begin
      // There's a 1^32 chance of the numbers being the same twice,
      // so we'll allow one failure
      lastrand = $random;
      for (i=0; i<`TRIES; i=i+1) begin
         thisrand = $random;
`ifdef TEST_VERBOSE
         $write("Random = %x\n", thisrand);
`endif
         if (thisrand == lastrand) same=same+1;
         lastrand = thisrand;
      end
      if (same > 1) begin
         $write("%%Error: Too many similar numbers: %d\n", same);
         $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
