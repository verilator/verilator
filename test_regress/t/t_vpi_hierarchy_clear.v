// ======================================================================
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty.
// SPDX-License-Identifier: CC0-1.0
// ======================================================================

module t (
    clk
);

  input clk;

  Sub sub (.clk(clk));

endmodule

module Sub (
    clk
);

  // this comment should get ignored for public-ignore
  input clk  /* verilator public_flat_rw */;

endmodule
