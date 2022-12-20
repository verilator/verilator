// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module x;
   typedef struct {
      int fst, snd;
   } uselessA_t;

   typedef struct {
      bit [3:0] n;
      uselessA_t b;
   } uselessB_t;

   uselessA_t useless;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
