// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  import "DPI-C" context function int dpii_add();

  virtual class uvm_sequence #(
      type RSP = int
  );
  endclass

  class Cls extends uvm_sequence #();
    virtual function void check_reg();
      int paths[$];
      int i;
      paths.push_back(1);
      paths.push_back(2);
      foreach (paths[p]) begin
        i = dpii_add();
      end
    endfunction
  endclass

  initial begin
    Cls c;
    int i;
    c = new;
    i = dpii_add();
    `checkd(i, 1);

    c.check_reg();

    i = dpii_add();
    `checkd(i, 4);
    $finish;
  end

endmodule
