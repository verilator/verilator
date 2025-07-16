// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define MAX 10

module t (/*AUTOARG*/
      clk
   );

   input clk;
   int cyc = 0;
   logic [`MAX:0] val = {`MAX+1{1'b0}};

   initial val[0] = 1;

   Test1 t1(clk, cyc, val);

   always @(posedge clk) begin
      cyc <= cyc + 1;

      $display("val = %20b", val);

      if (cyc < `MAX) begin
         val[cyc] <= 0;
         val[cyc+1] <= 1;
      end else begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test1 (
      clk,
      cyc,
      val
   );

   input clk;
   input [`MAX:0] val;
   input integer cyc;

   assert property(@(posedge clk) not (&val));

   assert property(@(posedge clk) (not ~|val));
endmodule
