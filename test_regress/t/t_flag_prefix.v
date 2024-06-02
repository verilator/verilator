// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module t;
   sub sub();
endmodule

module sub;
   // no_inline_module, so it goes into separate file
   /* verilator no_inline_module */

   // Goes into const pool which is separate file
   wire bit   [255:0] C = {32'h1111_1111,
                           32'h2222_2222,
                           32'h3333_3333,
                           32'h4444_4444,
                           32'h5555_5555,
                           32'h6666_6666,
                           32'h7777_7777,
                           32'h8888_8888};

   int  i;

   initial begin
      // Note: Base index via $c to prevent optimization
      i = $c(0*32); $display("0x%32x", C[i+:32]);
      i = $c(1*32); $display("0x%32x", C[i+:32]);
      i = $c(2*32); $display("0x%32x", C[i+:32]);
      i = $c(3*32); $display("0x%32x", C[i+:32]);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
