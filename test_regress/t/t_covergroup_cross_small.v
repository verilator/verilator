// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test small cross coverage with inline implementation

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int cyc = 0;

   logic [3:0] a;
   logic [3:0] b;

   covergroup cg @(posedge clk);
      option.per_instance = 1;

      // 2-way cross: 44 = 16 bins (< 64 threshold, should use inline)
      cp_a: coverpoint a {
         bins a0 = {0,1,2,3};
         bins a1 = {4,5,6,7};
         bins a2 = {8,9,10,11};
         bins a3 = {12,13,14,15};
      }

      cp_b: coverpoint b {
         bins b0 = {0,1,2,3};
         bins b1 = {4,5,6,7};
         bins b2 = {8,9,10,11};
         bins b3 = {12,13,14,15};
      }

      cross_ab: cross cp_a, cp_b;
   endgroup

   cg cg_inst = new;

   always @(posedge clk) begin
      cyc <= cyc + 1;

      a <= cyc[3:0];
      b <= cyc[7:4];

      if (cyc == 20) begin
         /* verilator lint_off IMPLICITSTATIC */
         real inst_cov = cg_inst.get_inst_coverage();
         /* verilator lint_on IMPLICITSTATIC */
         $display("Coverage: %0.1f%%", inst_cov);

         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
