// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   reg arr [15:0];
   reg mat [3:0] [3:0];

   initial begin
      for (int i = 0; i < 16; i++) begin
         arr[i] = ^i;
         mat[i/4][i%4] = ^i;
      end

      $display("%%p=%p", arr);
      $display("%%p=%p", mat);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
