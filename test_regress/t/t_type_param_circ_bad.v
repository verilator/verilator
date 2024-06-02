// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package pkg;
   parameter [7:0] WIDTH = 8;
   typedef logic [WIDTH-1:0] SZ;
endpackage // pkg

module t
  import pkg::*;
   # (parameter type SZ = SZ)
   (input SZ i,
    output SZ o);

   always_comb o = i;

endmodule
