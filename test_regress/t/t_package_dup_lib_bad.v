// DESCRIPTION: Verilator: First package declaration in a library
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

package shared_pkg;
  localparam int VALUE = 1;
endpackage

module t;
  import shared_pkg::VALUE;
  initial begin
    `checkh (VALUE, 1);
  end
endmodule
