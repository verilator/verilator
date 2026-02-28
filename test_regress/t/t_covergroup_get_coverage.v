// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
   int value = 0;

   covergroup cg;
      cp: coverpoint value {
         bins low = {[0:5]};
      }
   endgroup

   cg my_cg = new;

   always @(posedge clk) begin
      real cov;
      cov = my_cg.get_inst_coverage();
      my_cg.sample();
   end
endmodule
