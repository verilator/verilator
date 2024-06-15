// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls #(parameter PARAMB = 12);
endclass
class Cls2 #(parameter PARAMB = 13, parameter PARAMC = 14);
endclass

module t (/*AUTOARG*/);

   Cls #(.PARAMBAD(1)) c;  // Bad param name
   Cls #(13, 1) cd;  // Bad param number
   Cls #(.PARAMB(14),) ce;  // Bad superfluous comma
   Cls #(14,) cf;  // Bad superfluous comma
   Cls2 #(15,) cg;  // Bad superfluous comma
   Cls2 #(.PARAMB(16),) ch;  // Bad superfluous comma
   Cls2 #(.PARAMC(17),) ci;  // Bad superfluous comma

endmodule
