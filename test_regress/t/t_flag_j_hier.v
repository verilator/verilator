// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
   logic a;
   s u_s(.a(a));
endmodule

module s(output logic a);
   /*verilator hier_block*/
endmodule
