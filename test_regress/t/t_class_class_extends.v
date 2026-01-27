// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package uvm_pkg;
  typedef class uvm_root;

  virtual class uvm_coreservice_t;
    pure virtual function uvm_root get_root();
    static function uvm_coreservice_t get();
      return null;
    endfunction
  endclass

  class uvm_default_coreservice_t extends uvm_coreservice_t;
    virtual function uvm_root get_root();
      return uvm_root::m_uvm_get_root();
    endfunction
  endclass

  virtual class uvm_object;
  endclass

  class uvm_report_object extends uvm_object;
    // Note there's no 'virtual' on this function
    function uvm_report_object uvm_get_report_object();  // Wrong target
      return null;
    endfunction
  endclass

  class uvm_root extends uvm_report_object;
    static function uvm_root m_uvm_get_root();
      uvm_root top;
      top = new();
      return null;
    endfunction
  endclass

  virtual class uvm_process_guard_base extends uvm_object;
    pure virtual function void do_trigger();
    // Removing m_process member works around the issue
    protected process m_target_process;
    function new();
      m_target_process = process::self();
    endfunction
    function void m_process_guard(uvm_process_guard_base guard);
      // Removing fork/join works around the issue
      fork
        begin
          if (guard.m_target_process != null) begin
            guard.do_trigger();
          end
        end
      join_none
    endfunction
  endclass

  class uvm_process_guard #(
      type T = int
  ) extends uvm_process_guard_base;
    protected T m_context;
    function void do_trigger();
      m_context.process_guard_triggered(this);
    endfunction
  endclass

  class uvm_sequence_item;
    virtual function uvm_report_object uvm_get_report_object();  // Correct target
      uvm_coreservice_t cs = uvm_coreservice_t::get();
      return cs.get_root();
    endfunction
  endclass

  virtual class uvm_sequence_base extends uvm_sequence_item;
    typedef uvm_process_guard#(uvm_sequence_base) m_guard_t;
    function void process_guard_triggered(m_guard_t guard);
      uvm_pkg::uvm_report_object _local_report_object_arg_;
      _local_report_object_arg_ = uvm_get_report_object();
      //  ^ calls uvm_sequence_base->virtual uvm_sequence_item::uvm_get_report_object()
    endfunction
  endclass

  virtual class uvm_sequence #(
      type RSP = int
  ) extends uvm_sequence_base;
  endclass

endpackage

module t;

  import uvm_pkg::*;

  class Cls extends uvm_report_object;

    class transaction_sequence extends uvm_sequence #(uvm_object);
      virtual task body();
        uvm_pkg::uvm_report_object _local_report_object_arg_;
        _local_report_object_arg_ = uvm_get_report_object();
        //                          ^-  calls transaction_sequence->uvm_sequence
        // ->uvm_sequence_base->virtual uvm_sequence_item::uvm_get_report_object();
      endtask
    endclass

  endclass

  initial begin
    Cls c = new();
    $finish;
  end
endmodule
