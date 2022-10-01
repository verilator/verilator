// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;
   wire [5:0] a;
   assign (weak0, strong1) a = clk ? 'z : '0;
   assign (strong0, pull1) a = 6'b110001;
   initial begin
      if (a === 6'b110001) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
