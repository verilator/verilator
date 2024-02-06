// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
   reg [7:0] vec1 [3:0], vec2 [3:0];

   always
      for (int i = 0; i < 4; i++)
         vec2[i] = vec1[i];

   initial begin
      #1 vec1[0] = 8'h0f;
      #1 vec1[1] = 8'h04;
      #1 vec1[2] = 8'h0e;
      #1 vec1[3] = 8'h0a;

      #1
      for (int i = 0; i < 4; i++)
         if (vec1[i] != vec2[i]) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
