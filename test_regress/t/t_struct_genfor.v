// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t ();

   for (genvar g = 0; g < 2; ++g) begin : genfor
      typedef struct packed {
         logic [31:0] val1;
         logic [31:0] val2;
      } struct_t;
      struct_t forvar;

      initial begin
         forvar.val1 = 1;
         forvar.val2 = 2;
         if (forvar.val1 != 1) $stop;
         if (forvar.val2 != 2) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
