// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   logic a;
   s u_s(.a(a));
endmodule

module s(output logic a);
   /*verilator hier_block*/
endmodule
