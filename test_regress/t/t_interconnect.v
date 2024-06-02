// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Note: Other simulator's support for interconnect seems rare, the below might
// not be correct code.

module t(/*AUTOARG*/);

   interconnect a;
   interconnect b;

   moda suba (.a, .b);
   modb #(.TA_t(real)) subb (.a(a), .b(b));

endmodule

module moda
  (
   output interconnect a,
   output interconnect b);
   modaa subaa (.a, .b);
endmodule

module modaa
  (
   output real a,
   output int  b);
   initial begin
      a = 1.234;
      b = 1234;
   end
endmodule

module modb
  #(parameter type TA_t = int)
  (
   input TA_t a,
   input int b);
   initial begin
      #10;
      if (a != 1.234) $stop;
      if (b != 1234) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
