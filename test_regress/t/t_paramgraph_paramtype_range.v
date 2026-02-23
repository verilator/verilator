// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
// DESCRIPTION:
// Regression for localparam-derived cfg structs feeding interface instances
// and their nested typedefs.
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package TestPkg;
  localparam type tm_region_t = logic [1:0];
endpackage

module TestMod;
  import TestPkg::*;

  // This should work - tm_region_t has width 2
  localparam tm_region_t tm_region_lsio = 2'b10;

  // Test logic
  initial begin
    $display("tm_region_lsio = %b", tm_region_lsio);
    `checkd(tm_region_lsio, 2);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
