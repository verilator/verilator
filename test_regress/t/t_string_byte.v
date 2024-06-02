// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t(/*AUTOARG*/);

   // Unpacked byte from string IEEE 1800-2023 5.9
   byte bh[3:0] = "hi2";
   byte bl[0:3] = "lo2";

   initial begin
      `checkh(bh[0], "2");
      `checkh(bh[1], "i");
      `checkh(bh[2], "h");
      `checkh(bh[3], 0);
      `checkh(bl[0], 0);
      `checkh(bl[1], "l");
      `checkh(bl[2], "o");
      `checkh(bl[3], "2");
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
