// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls1;
   randc int rc;

   constraint c_bad { rc dist {3 := 0, 10 := 5}; }  // Bad, no dist on randc
endclass

module t;
endmodule
