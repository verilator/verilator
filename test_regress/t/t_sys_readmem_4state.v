// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;
   reg [3:0] MEMB [6];
   reg [3:0] MEMH [6];

   initial begin
      $readmemb("t/t_sys_readmem_4state.mem", MEMB);
      $display("MEMB=%p", MEMB);
      $writememh({`STRINGIFY(`TEST_OBJ_DIR),"/t_sys_readmem_4state_b.mem"}, MEMB);

      $readmemh("t/t_sys_readmem_4state.mem", MEMH);
      $display("MEMH=%p", MEMH);
      $writememh({`STRINGIFY(`TEST_OBJ_DIR),"/t_sys_readmem_4state_h.mem"}, MEMH);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
