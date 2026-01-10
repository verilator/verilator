// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class uvm_process_guard #(
    type T = int
);
  T m_context;
  extern function T get_context();
  extern function new(T ctxt);
endclass

// When this moves into class, note it's not uvm_process_guard#()::T
// but rather the T specific to the parameterized class
function uvm_process_guard::T uvm_process_guard::get_context();
  return this.m_context;
endfunction

function uvm_process_guard::new(uvm_process_guard::T ctxt);
  this.m_context = ctxt;
endfunction : new

class uvm_sequence_base;
  typedef uvm_process_guard#(uvm_sequence_base) m_guard_t;
endclass

module t;
  initial begin
    uvm_sequence_base c;
    c = new;
    $finish;
  end
endmodule
