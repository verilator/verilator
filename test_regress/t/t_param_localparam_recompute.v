// DESCRIPTION: Verilator: Reproducer for issue #7411.
//
// when V3Param widths a pin value against the port dtype the widthing must not
// edit any referenced template vars in place.  A dependent localparam like
// dirs_lp = dims_p*2+1 must still recompute from the overridden dims_p on
// each specialization.  (basically - don't poison the template)
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module sub #(
    parameter int dims_p = 2,
    parameter int dirs_lp = dims_p*2 + 1,
    parameter bit [1:0][dirs_lp-1:0][dirs_lp-1:0] matrix_p = '0
) ();
endmodule

module t;
  localparam bit [1:0][4:0][4:0] big_matrix = '1;
  localparam bit [1:0][2:0][2:0] small_matrix = '1;

  // First instance processes matrix_p with the template's default dims_p=2.
  // Before the fix, this froze dirs_lp on the template at 5.
  sub #(.matrix_p(big_matrix)) s1 ();

  // Second instance overrides dims_p=1, so dirs_lp must recompute to 3.
  sub #(.dims_p(1), .matrix_p(small_matrix)) s2 ();

  initial begin
    if (s1.dirs_lp !== 5) begin
      $write("%%Error: s1.dirs_lp=%0d expected 5\n", s1.dirs_lp);
      $stop;
    end
    if (s2.dirs_lp !== 3) begin
      $write("%%Error: s2.dirs_lp=%0d expected 3\n", s2.dirs_lp);
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
