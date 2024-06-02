// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   reg   _ranit;

   reg [2:0] a;
   reg [33:0] wide;
   reg        unused_r;

   initial _ranit = 0;

   always @ (posedge clk) begin : blockName
      begin     // Verify begin/begin is legal
         unused_r <= 1'b1;
      end
      begin end // Verify empty is legal
   end

   wire one = 1'b1;
   wire [7:0] rand_bits = 8'b01xx_xx10;

   always @ (posedge clk) begin
      if (!_ranit) begin
         _ranit <= 1;
         //
         a = 3'b1xx;
         wide <= 34'bx1_00000000_xxxxxxxx_00000000_xxxx0000;
         if (one !== 1'b1) $stop;
         if ((rand_bits & 8'b1100_0011) !== 8'b0100_0010) $stop;
         //
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   // verilator lint_off UNUSED
   wire _unused_ok = |{1'b1, wide};
   // verilator lint_on  UNUSED

endmodule
