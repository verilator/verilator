// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls1;
   randc int rc;

   constraint c_bad { soft rc > 4; }  // Bad, no soft on randc
endclass

module t;
endmodule
