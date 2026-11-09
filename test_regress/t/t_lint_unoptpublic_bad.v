// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package pkg;
  int pkg_sig  /*verilator public*/;  // <--- Warning
endpackage

module sub;
  int sig  /*verilator public*/;  // <--- Warning
  int flat_sig  /*verilator public_flat_rw*/;
  function int f;
    /*verilator public*/  // <--- Warning
    return sig + flat_sig;
  endfunction
endmodule

module pub_mod;
  /*verilator public_module*/  // <--- Warning
endmodule

module t;
  sub u_sub ();
  pub_mod u_pub_mod ();
endmodule
