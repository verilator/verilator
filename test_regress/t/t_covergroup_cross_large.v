// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test large cross coverage with sparse map implementation

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int cyc = 0;

   logic [3:0] a;
   logic [3:0] b;
   logic [3:0] c;
   logic [3:0] d;

   covergroup cg @(posedge clk);
      option.per_instance = 1;

      // Each coverpoint has 4 bins, total cross: 4444 = 256 bins
      // This exceeds threshold of 64, so should use sparse map
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

      cp_c: coverpoint c {
         bins c0 = {0,1,2,3};
         bins c1 = {4,5,6,7};
         bins c2 = {8,9,10,11};
         bins c3 = {12,13,14,15};
      }

      cp_d: coverpoint d {
         bins d0 = {0,1,2,3};
         bins d1 = {4,5,6,7};
         bins d2 = {8,9,10,11};
         bins d3 = {12,13,14,15};
      }

      // 4-way cross: 4444 = 256 bins (> 64 threshold)
      cross_abcd: cross cp_a, cp_b, cp_c, cp_d;
   endgroup

   cg cg_inst = new;

   always @(posedge clk) begin
      cyc <= cyc + 1;

      // Generate some cross coverage
      a <= cyc[3:0];
      b <= cyc[7:4];
      c <= cyc[3:0];  // Intentionally correlate some
      d <= cyc[7:4];

      if (cyc == 20) begin
         /* verilator lint_off IMPLICITSTATIC */
         real inst_cov = cg_inst.get_inst_coverage();
         /* verilator lint_on IMPLICITSTATIC */
         $display("Coverage: %0.1f%%", inst_cov);

         if (inst_cov < 1.0 || inst_cov > 100.0) begin
            $display("%%Error: Invalid coverage value");
            $stop;
         end

         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
