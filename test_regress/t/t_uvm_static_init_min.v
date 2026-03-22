// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package uvm_pkg;
  class uvm_cmdline_processor;
    static uvm_cmdline_processor m_inst;
    static function uvm_cmdline_processor get_inst();
      if (m_inst == null) m_inst = new;
      return m_inst;
    endfunction
    function int get_arg_values(string prefix, ref string values[$]);
      values.push_back({prefix, "ok"});
      return values.size();
    endfunction
  endclass

  // Mirrors UVM's package-level singleton handle.
  const uvm_cmdline_processor uvm_cmdline_proc = uvm_cmdline_processor::get_inst();

  class uvm_component;
    static string m_set_cl_verb_values[$];
    function new();
      m_set_cl_msg_args();
    endfunction
    function void m_set_cl_msg_args();
      m_set_cl_verb();
    endfunction
    function void m_set_cl_verb();
      uvm_cmdline_processor clp;
      clp = uvm_cmdline_processor::get_inst();
      if (m_set_cl_verb_values.size() == 0) begin
        void'(uvm_cmdline_proc.get_arg_values("+uvm_set_verbosity=", m_set_cl_verb_values));
      end
      if (clp == null) $stop;
    endfunction
  endclass

  class uvm_root extends uvm_component;
    static uvm_root m_inst;
    static function uvm_root get();
      if (m_inst == null) m_inst = new;
      return m_inst;
    endfunction
  endclass

  // This path forces uvm_root::new -> uvm_component::m_set_cl_verb.
  const uvm_root uvm_top = uvm_root::get();
endpackage

module t;
  import uvm_pkg::*;

  initial begin
    if (uvm_top == null) $stop;
    if (uvm_cmdline_proc == null) $stop;
    if (uvm_component::m_set_cl_verb_values.size() != 1) $stop;
    if (uvm_component::m_set_cl_verb_values[0] != "+uvm_set_verbosity=ok") $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
