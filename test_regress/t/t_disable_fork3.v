// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   initial begin
      fork begin
         fork begin
            #3 $stop;
         end join_none
         #1;
      end join_none
      #2 disable fork;
   end
   initial #4 $write("*-* All Finished *-*\n");
endmodule
