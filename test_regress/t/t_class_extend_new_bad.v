// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package uvm_pkg;
  virtual class uvm_component;
    function new(string name, uvm_component parent);
    endfunction
  endclass
  class uvm_sequencer_base extends uvm_component;
    function new(string name, int parent);
      super.new(name, parent);  // <- 'int' passed instead of 'uvm_component', no type error
    endfunction
  endclass
  class uvm_sequencer_param_base #(
      type REQ = int
  ) extends uvm_sequencer_base;
    function new(string name, uvm_component parent);
      super.new(name, parent);  // <- 'uvm_component' passed instead of 'int', no type error
    endfunction
  endclass
  class uvm_sequencer #(
      type REQ = int
  ) extends uvm_sequencer_param_base #(REQ);
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
  endclass
endpackage

package s_core_env_pkg;
  class s_core_p_base_vsequencer extends uvm_sequencer;
    function new(input string name, input uvm_component parent);
      super.new(name, parent);
    endfunction
  endclass
endpackage

package s_core_tests_pkg;
  import s_core_env_pkg::*;
endpackage

import uvm_pkg::*;
