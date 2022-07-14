// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
   wire  (weak0, weak1) a = clk === 1'b1 ? 1'b1 : 1'bz;

   always begin
      if (a === 1'bz) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
