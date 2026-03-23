// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//

// DESCRIPTION: Verilator: Test nested interface typedef access
// This replicates the pattern from a much larger design that was
// failing with the localparam changes - accessing a typedef from
// a doubly-nested interface
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package TestPkg;
  localparam type addr_t = logic [11:0];
  localparam addr_t STATUS = addr_t'('ha5);
endpackage

module TestMod;
  import TestPkg::*;

  initial begin
    `checkd(STATUS, 'ha5);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
