// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   reg [175:0] hex [15:0];

   initial begin
      $readmemh("t/t_sys_readmem_bad_addr.mem", hex);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
