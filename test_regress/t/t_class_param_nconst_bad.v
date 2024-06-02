// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls #(parameter PARAM = 12);
endclass

module t (/*AUTOARG*/);

   Cls #(.PARAM($random)) c;  // Bad param name

endmodule
