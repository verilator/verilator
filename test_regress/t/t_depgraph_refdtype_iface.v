// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
// DESCRIPTION:
// Regression for localparam-derived cfg structs feeding interface instances
// and their nested typedefs.
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface depgraph_if;
  typedef logic [3:0] nibble_t;
endinterface

module depgraph_top;
  depgraph_if ifc();

  typedef ifc.nibble_t nibble_t;

  nibble_t a;
  nibble_t b;
  logic [3:0] sum;

  assign sum = a + b;

  initial begin
    #1;
    `checkd($bits(nibble_t), 4);
    `checkd($bits(sum), 4);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
