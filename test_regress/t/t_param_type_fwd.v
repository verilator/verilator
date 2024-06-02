// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for trace file interface aliasing

module m;
   parameter type enum E_t;
   parameter type struct S_t;
   parameter type union U_t;
   parameter type class C_t;
   parameter type interface class IC_t;
endmodule

class Cls #(parameter type enum E_t,
            parameter type struct S_t,
            parameter type union U_t,
            parameter type class C_t,
            parameter type interface class IC_t);
endclass

module t (/*AUTOARG*/);
   // TODO proper test
endmodule
