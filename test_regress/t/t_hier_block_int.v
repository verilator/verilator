// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2025 by Antmicro. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t(/*AUTOARG*/
   // inputs
   clk
);
   input clk;

   byte out1;
   shortint out2;
   int out3;
   longint out4;
   integer out5;
   time out6;

   sub sub(out1, out2, out3, out4, out5, out6);

   always_ff @(posedge clk) begin
      if (out1 == 1 && out2 == 2 && out3 == 3 && out4 == 4 && out5 == 5 && out6 == 6) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $write("Mismatch\n");
         $stop;
      end
   end
endmodule

module sub(
   output byte out1,
   output shortint out2,
   output int out3,
   output longint out4,
   output integer out5,
   output time out6
); /*verilator hier_block*/
   assign out1 = 1;
   assign out2 = 2;
   assign out3 = 3;
   assign out4 = 4;
   assign out5 = 5;
   assign out6 = 6;
endmodule
