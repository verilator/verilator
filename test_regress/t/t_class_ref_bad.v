// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class ClsRight;
   string m_s;
endclass

module t (/*AUTOARG*/);
   string s;
   initial begin
      // verilator lint_off PKGNODECL
      s = ClsRigh::m_s;  // Bad typo
   end
endmodule
