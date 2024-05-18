// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module sub(
   // Outputs
   out,
   // Inputs
   clk
   );
   // verilator inline_module

   output [3:0] out /* <-- this variable has to be marked as having external refs */;
   input clk;

   reg [3:0] r;

   always @ (posedge clk)
      r <= 4'h1;
   assign out = r;
endmodule

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   reg [3:0] unused;

   sub sub1(unused, clk);

   integer cyc = 0;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
         `checkh(sub1.r, 4'h1);
         `checkh(sub1.out, 4'h1);
      end
      else if (cyc == 2) begin
         force sub1.r = 4'h2;
         force sub1.out = 4'h3;
      end
      else if (cyc == 3) begin
         `checkh(sub1.r, 4'h2);
         `checkh(sub1.out, 4'h3);
      end
      //
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
