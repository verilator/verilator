// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
   interface class inte;
      interface class bad_cannot_nest;
      endclass
   endclass
endclass

module t;
   Cls c;
endmodule
