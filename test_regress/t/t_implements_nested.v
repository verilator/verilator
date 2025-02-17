// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   // IEEE 2023 only disallows nested interface inside another interface, not
   // class
   interface class good_can_nest;
   endclass
endclass

module t (/*AUTOARG*/);
   Cls c;
endmodule
