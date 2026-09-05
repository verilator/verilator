// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Validates two out-of-bounds write guards:
//  - The _vl_insert_WI() guard for a destination whose width is not a multiple
//    of 32.  t_math_insert_bound.v covers the aligned case.
//  - The V3Unknown guard for a select whose index expression is around 32 bits
//    wide, where computing the index's maximum value can overflow.

module t (
   clk
);

   input clk;

   // Each struct is 480 bits (15 words) with `dat` last, so a write to the
   // nonexistent bit 500 lands on word 15, one past the end of the struct.
   typedef struct packed {
      logic [30:0]  idx;
      logic [448:0] dat;
   } s31_t;

   typedef struct packed {
      logic [31:0]  idx;
      logic [447:0] dat;
   } s32_t;

   typedef struct packed {
      logic [32:0]  idx;
      logic [446:0] dat;
   } s33_t;

   s31_t s31;
   s32_t s32;
   s33_t s33;

   always_ff @(posedge clk) begin : blk
      logic [443:0] v;
      int           sel;

      sel = 440;
      void'($value$plusargs("SEL=%d", sel));

      // Writes bits 471:440: the top four bits of `v`, then 28 that do not exist.
      v = '0;
      v[sel +: 32] = 32'hcafef00d;

      $write("v=%h\n", v[443:412]);

      // Bit 500 of `dat` does not exist.  Index it with widths around 32 bits.
      s31 = '0;
      s32 = '0;
      s33 = '0;

      // verilator lint_off WIDTHTRUNC
      s31.idx = 500;
      s31.dat[s31.idx] = 1'b1;

      s32.idx = 500;
      s32.dat[s32.idx] = 1'b1;

      s33.idx = 500;
      s33.dat[s33.idx] = 1'b1;
      // verilator lint_on WIDTHTRUNC

      $write("dat=%h %h %h\n", s31.dat[446:415], s32.dat[445:414], s33.dat[444:413]);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
