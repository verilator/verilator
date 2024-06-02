// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg [3:0] a, b;

   Test1 t1(clk, a, b);
   Test2 t2(clk, a, b);
   Test3 t3(clk, a, b);

   initial begin
      a = 0;
      b = 0;
   end

   always @(posedge clk) begin
      a <= a + 1;
      b = b + 1;

      $display("a = %0d, b = %0d, %0d == %0d", a, b, $sampled(a), $sampled(b));

      if (b >= 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module Test1(
   clk, a, b
   );

   input clk;
   input [3:0] a, b;

   assert property (@(posedge clk) $sampled(a) == $sampled(b));

endmodule

module Test2(
   clk, a, b
   );

   input clk;
   input [3:0] a, b;

   assert property (@(posedge clk) a == b);

endmodule

module Test3(
   clk, a, b
   );

   input clk;
   input [3:0] a, b;

   int         hits[10];

   assert property (@(posedge clk) a == b) hits[1]=1;
   assert property (@(posedge clk) a == b) else hits[2]=1;
   assert property (@(posedge clk) a == b) hits[3]=1; else hits[4]=1;

   assert property (@(posedge clk) a != b) hits[5]=1;
   assert property (@(posedge clk) a != b) else hits[6]=1;
   assert property (@(posedge clk) a != b) hits[7]=1; else hits[8]=1;

   final begin
      `checkd(hits[1], 1);
      `checkd(hits[2], 0);
      `checkd(hits[3], 1);
      `checkd(hits[4], 0);
      `checkd(hits[5], 0);
      `checkd(hits[6], 1);
      `checkd(hits[7], 0);
      `checkd(hits[8], 1);
   end

endmodule
