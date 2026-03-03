// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//

// Test case for REFDTYPE not linked to type
// This reproduces the error where a REFDTYPE in a parameter expression
// is not properly linked to its type after DepGraph resolution

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package Include;
  typedef logic [11:0] mbox_addr_t;
endpackage

interface mbox_if #(parameter int WIDTH = 0);
  typedef Include::mbox_addr_t mbox_addr_t;

  typedef struct packed {
    logic [1:0] tag;
    logic [WIDTH-1:0] addr;
  } RFTag;
endinterface

module mbox #(parameter int WIDTH = 0);
  mbox_if #(WIDTH) if_inst();

  // This should reproduce the REFDTYPE UNLINKED error
  // Using a type cast of an interface typedef in a parameter
  localparam logic [16:0] TAG_ZERO = {1'b1, if_inst.RFTag'(0)};

  initial begin
    `checkd($bits(TAG_ZERO), 17);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module top;
  mbox #(.WIDTH(14)) u_mbox();
endmodule
