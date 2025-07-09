// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef enum { ONE } e_t;

typedef struct { int m_i; } s_t;

typedef union { int m_i; } u_t;

class c_t;
endclass

interface class ic_t;
endclass

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

module t;
   sub #(.E_t(e_t), .S_t(s_t), .U_t(u_t), .C_t(c_t), .IC_t(ic_t)) sub();
   Cls #(.E_t(e_t), .S_t(s_t), .U_t(u_t), .C_t(c_t), .IC_t(ic_t)) c;
   initial begin
      c = new;
   end
endmodule
