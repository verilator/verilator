// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   logic [63:0] array = 64'hfeedf00d12345678;

   initial begin
      case ($c("1"))
        1: $stop;
        2: $stop;
        3: $stop;
        default: $stop;
      endcase

      $display("0x%8x", array[$c(0) +: 32]);
   end

endmodule
