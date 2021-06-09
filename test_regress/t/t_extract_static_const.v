// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   wire bit   [255:0] C = {32'h1111_1111,
                           32'h2222_2222,
                           32'h3333_3333,
                           32'h4444_4444,
                           32'h5555_5555,
                           32'h6666_6666,
                           32'h7777_7777,
                           32'h8888_8888};

   // Same values as above, but with different type
   wire logic [255:0] D = {32'h1111_1111,
                           32'h2222_2222,
                           32'h3333_3333,
                           32'h4444_4444,
                           32'h5555_5555,
                           32'h6666_6666,
                           32'h7777_7777,
                           32'h8888_8888};

   initial begin
      // Note: Base index via $c to prevent optimizatoin by Verilator
      $display("0x%32x", C[$c(0*32)+:32]);
      $display("0x%32x", D[$c(1*32)+:32]);
      $display("0x%32x", C[$c(2*32)+:32]);
      $display("0x%32x", D[$c(3*32)+:32]);
      $display("0x%32x", C[$c(4*32)+:32]);
      $display("0x%32x", D[$c(5*32)+:32]);
      $display("0x%32x", C[$c(6*32)+:32]);
      $display("0x%32x", D[$c(7*32)+:32]);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
