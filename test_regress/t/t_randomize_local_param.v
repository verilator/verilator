// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package Pkg;
  virtual class uvm_sequence #(
      type REQ = int
  );
    REQ m_req;
  endclass
endpackage

package SubPkg;
  import Pkg::*;
  class s_trgt_txn;
    int m_txn_val;
  endclass
  class p_mem_seq extends uvm_sequence #(s_trgt_txn);
    rand bit m_wr_flag;
    virtual task body();
      if (0 !== (m_req.randomize() with {local:: m_wr_flag;})) begin
      end
    endtask
  endclass
endpackage

module t;
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
