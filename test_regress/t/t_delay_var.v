// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   parameter PDLY = 1.2;
   real rdly = 1.3;
   integer idly = 1;

   reg in = 1'b0;

   wire #1.1 d_const = in;
   wire #idly d_int = in;
   wire #rdly d_real = in;
   wire #PDLY d_param = in;

   initial begin
      #2 in = 1'b0;
      #100;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
