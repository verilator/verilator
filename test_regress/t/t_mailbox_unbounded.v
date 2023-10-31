// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0
// verilator lint_off DECLFILENAME

module t(/*AUTOARG*/);
   mailbox #(int) m;
   int     msg = 0;
   int     out = 0;

   initial begin
      m = new;
      fork
         begin
            #10;  // So later then get() starts below
            msg = 1;
            if (m.try_put(msg) != 1) $stop;
         end
         begin
            m.get(out);
            if (out != 1) $stop;
         end
      join

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
