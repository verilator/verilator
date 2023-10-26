// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

interface if1 (
   if2 i1
);
endinterface

interface if2 (
   if1 i1
   // TODO: support recursive multiple modules and handle this in V3Param
);
endinterface

module t;
    //if1 if1();
endmodule
