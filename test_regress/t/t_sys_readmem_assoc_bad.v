// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   reg [5:0] assoc_bad_key[real];
   real assoc_bad_value[int];

   initial begin
      $readmemb("not", assoc_bad_key);
      $readmemb("not", assoc_bad_value);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
