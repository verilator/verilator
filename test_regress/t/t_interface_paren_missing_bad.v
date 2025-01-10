// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Goekce Aydos.
// SPDX-License-Identifier: CC0-1.0

// Interface instantiation without parenthesis

interface intf;
endinterface

module t;
   intf intf_i;
   initial $finish;
endmodule
