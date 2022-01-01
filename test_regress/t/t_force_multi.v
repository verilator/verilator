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

   logic [3:0] busa;
   logic [3:0] busb;

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         busa <= 4'b0101;
         busb <= 4'b0111;
      end
      else if (cyc == 1) begin
         force {busa, busb} = 8'b1111_1101;
      end
      else if (cyc == 2) begin
         `checkh(busa, 4'b1111);
         `checkh(busb, 4'b1101);
      end
      //
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
