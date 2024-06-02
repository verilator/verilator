// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module test(
            /*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cnt = 32'h12345678;
   int   cyc = 0;

   always @(posedge clk) begin
      if (cyc > 3) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end else begin
         cyc <= cyc + 1;
         cnt <= cnt + 1;
         $write("%08x\n", {16'h0, cnt[15: 0]});
         $write("%08x\n", {16'h0, cnt[31:16]});
      end
   end

endmodule
