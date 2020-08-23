// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   initial begin
      // Label checks
      begin : b1
      end : b1
      //
      b2 : begin
      end : b2
      // With no statements this is a NOP
      fork : f1
      join : f1
      //
      f2: fork
      join_any : f2
      //
      fork
      join_none
      // With one statement this is supported and optimized to a begin/end
      fork : fblk
         begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      join : fblk
   end

endmodule
