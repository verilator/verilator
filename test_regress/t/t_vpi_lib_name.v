// DESCRIPTION: Verilator: VPI names of variables in a library
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  sub u_sub ();
endmodule

`ifndef USE_LIB
module sub;
  /*verilator hier_block*/
  int count  /*verilator public_flat_rw*/ = 1;
  leaf u_leaf ();
  // The DPI scope of this instance has the same name as its VPI scope
  import "DPI-C" context function int dpic_check_scope();
  initial if (dpic_check_scope() != 0) $stop;
endmodule

module leaf;
  int last  /*verilator public_flat_rw*/ = 2;
endmodule
`endif
