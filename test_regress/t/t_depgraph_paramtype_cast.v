// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
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
