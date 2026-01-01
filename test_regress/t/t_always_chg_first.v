// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk, fastclk
   );

   input clk;
   input fastclk;       // surefire lint_off_line UDDIXN

   integer _mode;  initial _mode=0;

   reg  [31:0] ord1; initial ord1 = 32'h1111;
   wire [31:0] ord2;
   reg  [31:0] ord3;
   wire [31:0] ord4;
   wire [31:0] ord5;
   wire [31:0] ord6;
   wire [31:0] ord7;

   // verilator lint_off UNOPT
   t_chg_a a (
              .a(ord1), .a_p1(ord2),
              .b(ord4), .b_p1(ord5),
              .c(ord3), .c_p1(ord4),
              .d(ord6), .d_p1(ord7)
              );

   // surefire lint_off ASWEMB
   assign      ord6 = ord5 + 1;
   // verilator lint_on UNOPT

   always @ (/*AS*/ord2) ord3 = ord2 + 1;

   always @ (fastclk) begin // surefire lint_off_line ALWLTR ALWMTR
      if (_mode==1) begin
         //$write("[%0t] t_chg: %d: Values: %x %x %x %x %x %x %x\n", $time,fastclk,ord1,ord2,ord3,ord4,ord5,ord6,ord7);
         //if (ord2 == 2 && ord7 != 7) $stop;
      end
   end

   always @ (posedge clk) begin
      if (_mode==0) begin
         $write("[%0t] t_chg: Running\n", $time);
         _mode<=1;
         ord1 <= 1;
      end
      else if (_mode==1) begin
         _mode<=2;
         if (ord7 !== 7) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module t_chg_a (/*AUTOARG*/
   // Outputs
   a_p1, b_p1, c_p1, d_p1,
   // Inputs
   a, b, c, d
   );
   input [31:0] a;   output [31:0] a_p1;  wire [31:0] a_p1 = a + 1;
   input [31:0] b;   output [31:0] b_p1;  wire [31:0] b_p1 = b + 1;
   input [31:0] c;   output [31:0] c_p1;  wire [31:0] c_p1 = c + 1;
   input [31:0] d;   output [31:0] d_p1;  wire [31:0] d_p1 = d + 1;
endmodule
