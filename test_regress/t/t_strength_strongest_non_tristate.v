// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (clk1, clk2);
   input wire clk1;
   input wire clk2;

   wire (weak0, weak1) a = 0;
   assign (strong0, supply1) a = clk1;
   assign (pull0, pull1) a = 1;

   wire b;
   xor (strong0, strong1) (b, clk1, clk2);
   and (weak0, pull1) (b, clk1, clk2);

   wire [7:0] c;
   assign (supply0, strong1) c = clk1 ? '1 : '0;
   assign (weak0, supply1) c = '0;
   assign (weak0, pull1) c = 'z;

   always begin
      if (a === clk1 && b === clk1 ^ clk2 && c[0] === clk1) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $write("Error: a = %b, b = %b, c[0] = %b, ", a, b, c[0]);
         $write("expected: a = %b, b = %b, c[0] = %b\n", clk1, clk1 ^ clk2, clk1);
         $stop;
      end
   end
endmodule
