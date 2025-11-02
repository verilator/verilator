// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Jie Xu.
// SPDX-License-Identifier: CC0-1.0

// change these two parameters to see the speed differences
`define DATA_WIDTH 8
`define REP_COUNT4 `DATA_WIDTH/4
`define REP_COUNT2 `DATA_WIDTH/2


module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   reg [3:0] count4 = 0;
   reg [1:0] count2 = 0;

   reg [`DATA_WIDTH-1:0] a = {`REP_COUNT4{4'b0000}};
   reg [`DATA_WIDTH-1:0] b = {`REP_COUNT4{4'b1111}};
   reg [`DATA_WIDTH-1:0] c = {`REP_COUNT4{4'b1111}};
   reg [`DATA_WIDTH-1:0] d = {`REP_COUNT4{4'b1111}};
   reg [`DATA_WIDTH-1:0] res1;
   reg [`DATA_WIDTH-1:0] res2;
   reg [`DATA_WIDTH-1:0] res3;
   reg [`DATA_WIDTH-1:0] res4;

   drv1 t_drv1 [`DATA_WIDTH-1:0] (.colSelA(a), .datao(res1));
   drv2 t_drv2 [`DATA_WIDTH-1:0] (.colSelA(a), .colSelB(b), .datao(res2));
   drv3 t_drv3 [`DATA_WIDTH-1:0] (.colSelA(a), .colSelB(b), .colSelC(c), .datao(res3));
   drv4 t_drv4 [`DATA_WIDTH-1:0] (.colSelA(a), .colSelB(b), .colSelC(c), .colSelD(d), .datao(res4));

   always@(posedge clk)
   begin
       count2 <= count2 + 1;
       count4 <= count4 + 1;
       a <= {`REP_COUNT4{count4}};
       b <= {`REP_COUNT4{count4}};
       c <= {`REP_COUNT2{count2}};
       d <= {`REP_COUNT2{count2}};

       if (res1 != (a)) begin
       $stop;
       end
       if (res2 != (a&b)) begin
       $stop;
       end
       if (res3 != (a&b&c)) begin
       $stop;
       end
       if (res4 != (a&b&c&d)) begin
       $stop;
       end

       if (count4 > 10) begin
           $write("*-* All Finished *-*\n");
           $finish;
       end
   end
endmodule


module drv1
  (input colSelA,
   output datao
   );
   assign datao = colSelA;
endmodule

module drv2
  (input colSelA,
   input colSelB,
   output datao
   );
   assign datao = colSelB & colSelA;
endmodule

module drv3
  (input colSelA,
   input colSelB,
   input colSelC,
   output datao
   );
   assign datao = colSelB & colSelA & colSelC;

endmodule

module drv4
  (input colSelA,
   input colSelB,
   input colSelC,
   input colSelD,
   output datao
   );
   assign datao = colSelB & colSelA & colSelC & colSelD;

endmodule
