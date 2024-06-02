// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0


module t;
   initial begin
      int x = 0;
      while (x < 10) begin : outer_loop
         int y = 0;
         while (y < x) begin : inner_loop
            static int a = 0;
            a++;
            y++;
         end
         x++;
      end
      if (outer_loop.inner_loop.a != 45) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
