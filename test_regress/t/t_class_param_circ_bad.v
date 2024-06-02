// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef class ClsB;

class ClsA #(parameter PARAM = 12);
   ClsB #(PARAM+1) b;
endclass

class ClsB #(parameter PARAM = 12);
   ClsA #(PARAM+1) a;
endclass

module t (/*AUTOARG*/);

   ClsA #(.PARAM(15)) c;  // Bad param name

endmodule
