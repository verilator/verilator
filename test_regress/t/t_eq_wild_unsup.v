// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

function logic get_x_or_0(logic get_x);
   return get_x ? 1'bx : 1'b0;
endfunction

module t;
   initial begin
      if (1 ==? get_x_or_0(0)) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
