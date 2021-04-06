// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

config cfgBad;
   design rtlLib.top;
   default liblist rtlLib;
   instance top.a2 liblist gateLib;
   include none;
   library rtlLib *.v;
   include aa;
   use gateLib;
   cell rtlLib.cell;
endconfig

module t;
endmodule
