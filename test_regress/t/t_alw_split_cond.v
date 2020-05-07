// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

//bug1604
module t (/*AUTOARG*/
   // Outputs
   two,
   // Inputs
   clk, aresetn, ten
   );

   input wire clk;
   input wire aresetn;

   input reg [9:0] ten;
   output reg [1:0] two;

   // Passes with this
   //output reg [1:0] rx;
   //output reg [1:0] ry;

   function [1:0] func
     (
      input [1:0] p0_x,
      input [1:0] p0_y,
      input [1:0] p1_x,
      input [1:0] p1_y,
      input [1:0] sel);

      reg [1:0]   rx;
      reg [1:0]   ry;

`ifdef NOT_DEF
      // This way works
      rx = sel == 2'b10 ? p1_x : p0_x;
      ry = sel == 2'b10 ? p1_y : p0_y;
`else
      // This way fails to compile
      if (sel == 2'b10) begin
         rx = p1_x;
         ry = p1_y;
      end
      else begin
         rx = p0_x;
         ry = p0_y;
      end
`endif
      // Note rx and ry are unused
      //func = rx | ry;  // Also passes
      func = 0;
   endfunction

   always @(*) begin
      two = func(
                 ten[8 +: 2],
                 ten[6 +: 2],
                 ten[4 +: 2],
                 ten[2 +: 2],
                 ten[0 +: 2]);
   end
endmodule
