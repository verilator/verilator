// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package pkg;
  typedef int unsigned id_t;
  localparam id_t DEFAULT_ID = 7;
  // Typically from a file included into the package
  import pkg::*;
  class Cls;
    id_t id;
    function new();
      id = DEFAULT_ID;
    endfunction
    function int get_id();
      import pkg::DEFAULT_ID;  // Class within the package importing the package
      return DEFAULT_ID;
    endfunction
  endclass
endpackage

module t;
  import pkg::*;
  initial begin
    Cls c;
    c = new;
    `checkd(c.id, 7);
    `checkd(c.get_id(), 7);
    `checkd(DEFAULT_ID, 7);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
