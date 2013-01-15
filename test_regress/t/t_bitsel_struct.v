// DESCRIPTION: Verilator: Verilog Test module
//
// A test case for struct signal bit selection.
//
// This test is to check that bit selection of multi-dimensional signal inside
// of a struct works.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Jie Xu.

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   typedef struct packed {
       logic [1:0][15:0] channel;
       logic others;
   } buss_t;

   buss_t b;
   reg [7:0] a;

   initial begin
      b = {16'h8765,16'h4321,1'b1};
      a = b.channel[0][8+:8];
      if (a != 8'h43) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
