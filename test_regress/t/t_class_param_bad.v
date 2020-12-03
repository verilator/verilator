// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls #(parameter PARAMB = 12);
endclass

module t (/*AUTOARG*/);

   Cls #(.PARAMBAD(1)) c;  // Bad param name
   Cls #(13, 1) cd;  // Bad param number

endmodule
