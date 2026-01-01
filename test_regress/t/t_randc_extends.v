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
    randc bit [15:0] select_randc;  // Passes without randc here
    task body();
      if (0 == randomize(select_randc)) begin
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
    c.body;
    $finish;
  end

endmodule
