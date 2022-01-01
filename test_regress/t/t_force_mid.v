// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t(/*AUTOARG*/
   // Outputs
   tried,
   // Inputs
   clk
   );

   input clk;
   output [3:0] tried;

   integer cyc = 0;

   assign tried = 4'b0101;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         if (tried != 4'b0101) $stop;
      end
      else if (cyc == 1) begin
         force tried = 4'b1010;
      end
      else if (cyc == 2) begin
         if (tried != 4'b1010) $stop;
      end
      //
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
