// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module M #(
    parameter int P = 12,
    parameter int Q = 13
    ) (
    input wire i,
    output wire o
    );
    assign o = i;
endmodule

module N #(
    parameter int P = 12
    ) (
    input wire i,
    output wire o
    );
    assign o = i;
endmodule

module t (/*AUTOARG*/);

  wire i1, o1, i2, o2, i3, o3, i4, o4, i5, o5, i6, o6;

   // All of these have superfluous commas after the first parameter.
   // All of the N instances produced a PINNOTFOUND error, however as reported in issue #4979,
   // none of the M instances do when they should. The copmma after the first parameter is not
   // allowed in verilog.

   M #(.P(13),) m1(
    .i(i1),
    .o(o1)
   );

   M #(14,) m2 (
    .i(i2),
    .o(o2)
    );

   M #(14,) m3 (
    .i(i3),
    .o(o3)
    );

   N #(.P(13),) n1(
    .i(i4),
    .o(o4)
   );

   N #(14,) n2 (
    .i(i5),
    .o(o5)
    );

   N #(14,) n3 (
    .i(i6),
    .o(o6)
    );

endmodule
