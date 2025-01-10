// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int cyc;

   Sub sub ();

   default disable iff (cyc[0]);

   int a_false;
   always @(posedge clk iff !cyc[0]) begin
      if (cyc < 4 || cyc > 9) ;
      else a_false = a_false + 1;
   end

   int a0_false;
   a0: assert property (@(posedge clk) disable iff (cyc[0]) (cyc < 4 || cyc > 9))
     else a0_false = a0_false + 1;

   int a1_false;
   // Note that Verilator supports $inferred_disable in general expression locations
   // This is a superset of what IEEE specifies
   a1: assert property (@(posedge clk) disable iff ($inferred_disable) (cyc < 4 || cyc > 9))
     else a1_false = a1_false + 1;

   int a2_false;
   // Implicitly uses $inferred_disable
   a2: assert property (@(posedge clk) (cyc < 4 || cyc > 9))
     else a2_false = a2_false + 1;

   int a3_false;
   // A different disable iff expression
   a3: assert property (@(posedge clk) disable iff (cyc == 5) (cyc < 4 || cyc > 9))
     else a3_false = a3_false + 1;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 20) begin
         `checkd(a_false, 3);
         `checkd(a0_false, a_false);
         `checkd(a1_false, a_false);
         `checkd(a2_false, a_false);
         `checkd(a3_false, 5);
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module Sub;

   initial begin
      if ($inferred_disable !== 0) $stop;
   end

endmodule
