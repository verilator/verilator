// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class ex;
  randc struct {logic m_x;} s;  // <--- Bad: randc illegal on unpacked struct

  randc struct packed {logic m_x;} p_s;  // Ok
endclass : ex

module foo;
  initial begin
    ex e;
    void'(e.randomize());
  end
endmodule
