// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package s_pkg;
  typedef enum bit [4:0] {MEM_REQ = 5'b00000} P_Type_e;
endpackage

package pkg;
  import s_pkg::*;

  virtual class uvm_sequence #(
      type REQ = int
  );
    REQ m_req;
  endclass

  class cls_txn;
    P_Type_e m_type;
  endclass

  class cls_seq extends uvm_sequence #(cls_txn);
  endclass

  class p_mem_seq extends cls_seq;
    virtual task body();
      if (0 == (m_req.randomize() with {m_req.m_type == MEM_REQ;})) begin
      end
    endtask
  endclass
endpackage
