// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class ClsRight;
   string m_s;
endclass

module t;
   string s;
   initial begin
      // verilator lint_off PKGNODECL
      s = ClsRigh::m_s;  // Bad typo, issue #5475
   end
endmodule
