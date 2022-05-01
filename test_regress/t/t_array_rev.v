// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2016 by Geoff Barrett.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer      cyc = 0;
   // verilator lint_off LITENDIAN
   logic arrd [0:1] = '{ 1'b1, 1'b0 };
   // verilator lint_on LITENDIAN
   logic y0, y1;
   logic localbkw [1:0];

   arr_rev arr_rev_u (
     .arrbkw    (arrd),
     .y0(y0),
     .y1(y1)
   );

   always @ (posedge clk) begin
      if (arrd[0] != 1'b1) $stop;
      if (arrd[1] != 1'b0) $stop;

      localbkw = arrd;
`ifdef TEST_VERBOSE
      $write("localbkw[0]=%b\n", localbkw[0]);
      $write("localbkw[1]=%b\n", localbkw[1]);
`endif
      if (localbkw[0] != 1'b0) $stop;
      if (localbkw[1] != 1'b1) $stop;

`ifdef TEST_VERBOSE
      $write("y0=%b\n", y0);
      $write("y1=%b\n", y1);
`endif
      if (y0 != 1'b0) $stop;
      if (y1 != 1'b1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module arr_rev
  (
   input  var logic arrbkw [1:0],
   output var logic y0,
   output var logic y1
   );

   always_comb y0 = arrbkw[0];
   always_comb y1 = arrbkw[1];

endmodule
