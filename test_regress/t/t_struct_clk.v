// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

typedef struct {
   logic       clk1;
   logic       clk2;
   logic       rst;
} clks_t;

module t(/*AUTOARG*/
   // Inputs
   clk, fastclk
   );
   input clk;
   input fastclk;

   int cyc = 0;

   clks_t clks;
   always_comb begin
      clks.clk1 = clk;
      clks.clk2 = fastclk;
   end

   // verilator lint_off MULTIDRIVEN
   int cyc1 = 0;
   int cyc2 = 0;

   always @ (negedge clks.clk1) cyc1 <= cyc1 + 1;
   always @ (negedge clks.clk2) cyc2 <= cyc2 + 1;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc < 10) begin
         cyc1 <= '0;
         cyc2 <= '0;
      end
      else if (cyc == 99) begin
         `checkd(cyc1, 90);
         `checkd(cyc2, 90*5);

         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
