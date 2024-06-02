// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   o_29,o_29_old,
   o_30,o_30_old,
   o_31,o_31_old,
   o_32,o_32_old,
   o_59,o_59_old,
   o_60,o_60_old,
   o_62,o_62_old,
   o_64,o_64_old,
   o_119,o_119_old,
   o_120,o_120_old,
   o_121,o_121_old,
   o_127,o_127_old,
   o_128,o_128_old,
   o_255,o_255_old,
   o_256,o_256_old,
   // Inputs
   i_29,i_29_old,
   i_30,i_30_old,
   i_31,i_31_old,
   i_32,i_32_old,
   i_59,i_59_old,
   i_60,i_60_old,
   i_62,i_62_old,
   i_64,i_64_old,
   i_119,i_119_old,
   i_120,i_120_old,
   i_121,i_121_old,
   i_127,i_127_old,
   i_128,i_128_old,
   i_255,i_255_old,
   i_256,i_256_old
   );
   input [255:0]        i_29;
   output wire [255:0]  o_29;
   input [255:0]        i_29_old;
   output wire [255:0]  o_29_old;
   input [255:0]        i_30;
   output wire [255:0]  o_30;
   input [255:0]        i_30_old;
   output wire [255:0]  o_30_old;
   input [255:0]        i_31;
   output wire [255:0]  o_31;
   input [255:0]        i_31_old;
   output wire [255:0]  o_31_old;
   input [255:0]        i_32;
   output wire [255:0]  o_32;
   input [255:0]        i_32_old;
   output wire [255:0]  o_32_old;
   input [255:0]        i_59;
   output wire [255:0]  o_59;
   input [255:0]        i_59_old;
   output wire [255:0]  o_59_old;
   input [255:0]        i_60;
   output wire [255:0]  o_60;
   input [255:0]        i_60_old;
   output wire [255:0]  o_60_old;
   input [255:0]        i_62;
   output wire [255:0]  o_62;
   input [255:0]        i_62_old;
   output wire [255:0]  o_62_old;
   input [255:0]        i_64;
   output wire [255:0]  o_64;
   input [255:0]        i_64_old;
   output wire [255:0]  o_64_old;
   input [255:0]       i_119;
   output wire [255:0] o_119;
   input [255:0]       i_119_old;
   output wire [255:0] o_119_old;
   input [255:0]       i_120;
   output wire [255:0] o_120;
   input [255:0]       i_120_old;
   output wire [255:0] o_120_old;
   input [255:0]       i_121;
   output wire [255:0] o_121;
   input [255:0]       i_121_old;
   output wire [255:0] o_121_old;
   input [255:0]       i_127;
   output wire [255:0] o_127;
   input [255:0]       i_127_old;
   output wire [255:0] o_127_old;
   input [255:0]       i_128;
   output wire [255:0] o_128;
   input [255:0]       i_128_old;
   output wire [255:0] o_128_old;
   input [255:0]       i_255;
   output wire [255:0] o_255;
   input [255:0]       i_255_old;
   output wire [255:0] o_255_old;
   input [255:0]       i_256;
   output wire [255:0] o_256;
   input [255:0]       i_256_old;
   output wire [255:0] o_256_old;

   sub sub (.*);
endmodule

module sub (/*AUTOARG*/
   // Outputs
   o_29,o_29_old,
   o_30,o_30_old,
   o_31,o_31_old,
   o_32,o_32_old,
   o_59,o_59_old,
   o_60,o_60_old,
   o_62,o_62_old,
   o_64,o_64_old,
   o_119,o_119_old,
   o_120,o_120_old,
   o_121,o_121_old,
   o_127,o_127_old,
   o_128,o_128_old,
   o_255,o_255_old,
   o_256,o_256_old,
   // Inputs
   i_29,i_29_old,
   i_30,i_30_old,
   i_31,i_31_old,
   i_32,i_32_old,
   i_59,i_59_old,
   i_60,i_60_old,
   i_62,i_62_old,
   i_64,i_64_old,
   i_119,i_119_old,
   i_120,i_120_old,
   i_121,i_121_old,
   i_127,i_127_old,
   i_128,i_128_old,
   i_255,i_255_old,
   i_256,i_256_old
   );

   input [255:0]        i_29;
   output wire [255:0]  o_29;
   input [255:0]        i_29_old;
   output wire [255:0]  o_29_old;
   input [255:0]        i_30;
   output wire [255:0]  o_30;
   input [255:0]        i_30_old;
   output wire [255:0]  o_30_old;
   input [255:0]        i_31;
   output wire [255:0]  o_31;
   input [255:0]        i_31_old;
   output wire [255:0]  o_31_old;
   input [255:0]        i_32;
   output wire [255:0]  o_32;
   input [255:0]        i_32_old;
   output wire [255:0]  o_32_old;
   input [255:0]        i_59;
   output wire [255:0]  o_59;
   input [255:0]        i_59_old;
   output wire [255:0]  o_59_old;
   input [255:0]        i_60;
   output wire [255:0]  o_60;
   input [255:0]        i_60_old;
   output wire [255:0]  o_60_old;
   input [255:0]        i_62;
   output wire [255:0]  o_62;
   input [255:0]        i_62_old;
   output wire [255:0]  o_62_old;
   input [255:0]        i_64;
   output wire [255:0]  o_64;
   input [255:0]        i_64_old;
   output wire [255:0]  o_64_old;
   input [255:0]       i_119;
   output wire [255:0] o_119;
   input [255:0]       i_119_old;
   output wire [255:0] o_119_old;
   input [255:0]       i_120;
   output wire [255:0] o_120;
   input [255:0]       i_120_old;
   output wire [255:0] o_120_old;
   input [255:0]       i_121;
   output wire [255:0] o_121;
   input [255:0]       i_121_old;
   output wire [255:0] o_121_old;
   input [255:0]       i_127;
   output wire [255:0] o_127;
   input [255:0]       i_127_old;
   output wire [255:0] o_127_old;
   input [255:0]       i_128;
   output wire [255:0] o_128;
   input [255:0]       i_128_old;
   output wire [255:0] o_128_old;
   input [255:0]       i_255;
   output wire [255:0] o_255;
   input [255:0]       i_255_old;
   output wire [255:0] o_255_old;
   input [255:0]       i_256;
   output wire [255:0] o_256;
   input [255:0]       i_256_old;
   output wire [255:0] o_256_old;

   assign o_29 = i_29;
   assign o_29_old = i_29_old;

   assign o_30 = i_30;
   assign o_30_old = i_30_old;

   assign o_31 = i_31;
   assign o_31_old = i_31_old;

   assign o_32 = i_32;
   assign o_32_old = i_32_old;

   assign o_59 = i_59;
   assign o_59_old = i_59_old;

   assign o_60 = i_60;
   assign o_60_old = i_60_old;

   assign o_62 = i_62;
   assign o_62_old = i_62_old;

   assign o_64 = i_64;
   assign o_64_old = i_64_old;

   assign o_119 = i_119;
   assign o_119_old = i_119_old;

   assign o_120 = i_120;
   assign o_120_old = i_120_old;

   assign o_121 = i_121;
   assign o_121_old = i_121_old;

   assign o_127 = i_127;
   assign o_127_old = i_127_old;

   assign o_128 = i_128;
   assign o_128_old = i_128_old;

   assign o_255 = i_255;
   assign o_255_old = i_255_old;

   assign o_256 = i_256;
   assign o_256_old = i_256_old;

endmodule
