// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef int int_t;

module sub;
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
   sub #(.E_t(int_t), .S_t(int_t), .U_t(int_t), .C_t(int_t), .IC_t(int_t)) sub();
   Cls #(.E_t(int_t), .S_t(int_t), .U_t(int_t), .C_t(int_t), .IC_t(int_t)) c;
   initial begin
      c = new;
   end
endmodule
