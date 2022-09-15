// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (clk1, clk2);
   input wire clk1;
   input wire clk2;

   wire a;
   nor (pull0, weak1) n1(a, 0, 0);
   assign (strong0, weak1) a = 0;

   wire [1:0] b;
   assign (weak0, supply1) b = '1;
   assign b = clk1 ? '0 : 'z;

   wire c = 1;
   assign (weak0, pull1) c = clk1 & clk2;

   always begin
      if (!a && b === '1 && c) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $write("Error: a = %b, b = %b, c = %b ", a, b, c);
         $write("expected: a = 0, b = 11, c = 1\n");
         $stop;
      end
   end
endmodule
