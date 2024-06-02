// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   reg [175:0] hex [15:0];

   integer   i;

   initial begin
      // No warning as has addresses
      $readmemh("t/t_sys_readmem_bad_end2.mem", hex, 0, 15);
      // Warning as wrong end address
      $readmemh("t/t_sys_readmem_bad_end.mem", hex, 0, 15);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
