// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  virtual class uvm_object;
  endclass

  class config_obj extends uvm_object;
    function void pre_randomize();
      super.pre_randomize();
    endfunction
    function void post_randomize();
      super.post_randomize();
    endfunction
  endclass

  initial $finish;

endmodule
