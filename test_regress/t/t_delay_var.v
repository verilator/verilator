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
      #2 in = 1'b1;
      #100;
      if (d_const != 1) $stop;
      if (d_int != 1) $stop;
      if (d_real != 1) $stop;
      if (d_param != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
