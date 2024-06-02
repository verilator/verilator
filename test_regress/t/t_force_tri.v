// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   logic [3:0] bus;

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         bus <= 4'b0101;
      end
      else if (cyc == 1) begin
         force bus = 4'bzz10;
      end
      else if (cyc == 2) begin
         `checkh(bus, 4'bzz10);
      end
      //
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
