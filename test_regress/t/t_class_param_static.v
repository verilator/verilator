// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  class uvm_sequence_library #(
      type REQ = int,
      RSP = int
  );
    int sequences[$];
  endclass

  class Cls extends uvm_sequence_library;

    static int m_typewide_sequences[$];

    function void init_sequence_library();
      foreach (m_typewide_sequences[i]) sequences.push_back(m_typewide_sequences[i]);
    endfunction
  endclass

  initial begin
    Cls c;
    c = new;
    $finish;
  end

endmodule
