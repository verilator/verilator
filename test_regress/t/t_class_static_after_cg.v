// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  class Cls;
    // verilator lint_off COVERIGN
    covergroup cov_trans;
      option.per_instance = 1;
    endgroup

    virtual function void perform_transfer_checks();
      check_transfer_size();
    endfunction
    virtual function void check_transfer_size();
    endfunction
  endclass

  initial begin
    Cls c;
    c = new;
    c.perform_transfer_checks();
    $finish;
  end
endmodule
