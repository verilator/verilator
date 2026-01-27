// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface Ifc;
endinterface

module Sub;
   Ifc a();
endmodule

module t;
   Sub sub();
   // Issue #5649
   wire wbad = sub.a;
endmodule
