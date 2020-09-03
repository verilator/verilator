// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t
   (
   output wire o,
   input wire i,
   input wire i2
   );

   sub
     #(,  // Not found
       .NEXIST(1),  // Not found
       .P(2),
       .P(3))  // Dup
   sub (.o(o),
        .i(i),
        .i(i2),  // Dup
        .nexist(i2)  // Not found
        );

endmodule

module sub
  #(parameter P=1,
    parameter EXIST=9)
  (
   output wire o,
   input wire i,
   input wire exists
   );

   assign o = ~i;

endmodule
