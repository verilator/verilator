// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef struct {
   logic         bist;
   logic [38:0]  web;
   logic         ceb;
} mem_t;

module sub
  (input bist_0,
   input bist_1,
   input bist_2,
   output y
   );
   assign y = bist_0 | bist_1 | bist_2;
endmodule

module t
  (input mem_t i_ram_mbist [7:0],
   output y
   );
   sub sub
     (.y,
      .bist_0(i_ram_mbist[0].bist),
      .bist_1(i_ram_mbist[1].bist),
      .bist_2(i_ram_mbist[2].bist)
      );
endmodule
