// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package uvm_pkg;
  class uvm_reg_sequence #(
      type BASE = int
  );
    typedef enum {
      LOCAL = 2,
      UPSTREAM = 3
    } seq_parent_e;
  endclass
endpackage

module t;
  import uvm_pkg::*;
  class test_seq extends uvm_reg_sequence;
  endclass
  initial begin
    test_seq c;
    c = new;
    `checkd(c.LOCAL, 2);
    `checkd(c.UPSTREAM, 3);
    $finish;
  end
endmodule
