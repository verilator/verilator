// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;

   reg [5:0] assoc_c[int];
   reg [95:0] assoc_w[int];

   initial begin
      assoc_c[300] = 10;  // See if clearing must happen first
      $readmemb("t/t_sys_readmem_b.mem", assoc_c);
      $display("assoc_c=%p", assoc_c);
      $writememh({`STRINGIFY(`TEST_OBJ_DIR),"/t_sys_writemem_c_b.mem"}, assoc_c);

      $readmemb("t/t_sys_readmem_b.mem", assoc_w);
      // Not conditional with TEST_VERBOSE as found bug with wide display
      $display("assoc_w=%p", assoc_w);
      $writememh({`STRINGIFY(`TEST_OBJ_DIR),"/t_sys_writemem_w_h.mem"}, assoc_w);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
