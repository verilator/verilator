// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

function bit get_1_or_0(bit get_1);
   return get_1 ? 1'b1 : 1'b0;
endfunction

module t (/*AUTOARG*/);

   initial begin
      if (get_1_or_0(0) ==? get_1_or_0(1)) $stop;
      if (!(get_1_or_0(0) !=? get_1_or_0(1))) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
