// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package uvm_pkg;

  virtual class uvm_sequence #(
      type REQ = int
  );
  endclass

  class uvm_sequence_library #(
      type REQ = int
  ) extends uvm_sequence #(REQ);
    rand bit [15:0] m_rand;
    randc bit [15:0] m_randc;
    task body();
      if (0 == randomize(m_rand)) begin
      end
      if (0 == randomize(m_randc)) begin
      end
    endtask
  endclass
endpackage

module t;
  import uvm_pkg::*;

  class t1 extends uvm_sequence_library;
  endclass

  initial begin
    t1 c;
    c = new;
    $finish;
  end

endmodule
