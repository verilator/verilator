// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module m();
  module m_in_m;
  endmodule
  program p_in_m();
  endprogram
  interface i_in_m();
  endinterface
endmodule

interface i();
  interface i_in_i();
  endinterface
  program p_in_i();
  endprogram
endinterface
