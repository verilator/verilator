// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package uvm_pkg;
  class uvm_sequence_item;
  endclass
endpackage

package tb_cpu_pkg;
  import uvm_pkg::*;
  class tb_cpu_seq_item extends uvm_sequence_item;
    function void pre_randomize();
      super.pre_randomize();
    endfunction
    function void post_randomize();
      super.post_randomize();
    endfunction
  endclass
endpackage
