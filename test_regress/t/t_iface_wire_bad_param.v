// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface Ifc;
endinterface

module Sub #(parameter P);
   Ifc a();
endmodule

module t;
   Sub #(0) sub();
   wire wbad = sub.a;
endmodule
