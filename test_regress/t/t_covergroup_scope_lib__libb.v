// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module m2;
  m3 u_23 ();
endmodule

module m3;  // Module name duplicated between libraries
  covergroup cg with function sample (bit v);
    cp: coverpoint v;
  endgroup
  cg inst = new;
endmodule
