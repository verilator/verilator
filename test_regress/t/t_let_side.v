// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   let F(a) = {a, a, a};

   function byte g();
      static byte r = 0;
      return ++r;
   endfunction

   bit [23:0]     res;

   initial begin
      res = F(g());
      $display("%h", res);
      // Commercial1     010101 -- seems wrong by my reading of IEEE but anyhow
      // Commercial2/Vlt 010203
      // Commercial3/4   030201
      if (res != 24'h010101 && res != 24'h010203 && res != 24'h030201) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
