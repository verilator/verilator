// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   covergroup cg;
      cp_a: coverpoint 1'b0 { bins b0 = {0}; bins b1 = {1}; }
      cp_b: coverpoint 1'b0 { bins b0 = {0}; bins b1 = {1}; }
      cross_ab: cross cp_a, cp_b {
         option.per_instance = 1;  // unsupported for cross; triggers COVERIGN
      }
   endgroup
   cg cg_i = new;
   initial begin
      cg_i.sample();
      $finish;
   end
endmodule
