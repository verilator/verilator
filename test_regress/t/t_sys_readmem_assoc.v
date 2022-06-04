// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   int   cyc;

   reg [5:0] assoc_c[int];
   reg [95:0] assoc_w[int];

   always_ff @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
         assoc_c[300] <= 10;  // See if clearing must happen first
         // Also checks no BLKANDNBLK due to readmem/writemem
      end
      else if (cyc == 2) begin
         $readmemb("t/t_sys_readmem_b.mem", assoc_c);
         $display("assoc_c=%p", assoc_c);
         $writememh({`STRINGIFY(`TEST_OBJ_DIR),"/t_sys_writemem_c_b.mem"}, assoc_c);
      end
      else if (cyc == 3) begin
         $readmemb("t/t_sys_readmem_b.mem", assoc_w);
         // Not conditional with TEST_VERBOSE as found bug with wide display
         $display("assoc_w=%p", assoc_w);
         $writememh({`STRINGIFY(`TEST_OBJ_DIR),"/t_sys_writemem_w_h.mem"}, assoc_w);
      end
      else if (cyc == 4) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
