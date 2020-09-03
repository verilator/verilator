// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Rod Steward.
// SPDX-License-Identifier: CC0-1.0

module IOBUF ( input T, input I, output O, inout IO );
   assign O = IO;
   assign IO = T ? 1'bz : I;
endmodule

module t
  (
   input [7:0]  inlines,
   output [7:0] outlines,
   inout [7:0]  iolines,

   input        inctrl
   );

   generate for (genvar i = 4; i < 8; i = i+1) begin: Gen_D
      IOBUF d ( .T(inctrl), .I(inlines[i]), .O(outlines[i]), .IO(iolines[i]) );
      pullup d_pup (iolines[i]);
   end
   endgenerate

   IOBUF d_0 ( .T(inctrl), .I(inlines[0]), .O(outlines[0]), .IO(iolines[0]) );
   pullup d_0_pup (iolines[0]);

   IOBUF d_1 ( .T(inctrl), .I(inlines[1]), .O(outlines[1]), .IO(iolines[1]) );
   pullup d_1_pup (iolines[1]);

   IOBUF d_2 ( .T(inctrl), .I(inlines[2]), .O(outlines[2]), .IO(iolines[2]) );
   pullup d_2_pup (iolines[2]);

   IOBUF d_3 ( .T(inctrl), .I(inlines[3]), .O(outlines[3]), .IO(iolines[3]) );
   pullup d_3_pup (iolines[3]);

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
