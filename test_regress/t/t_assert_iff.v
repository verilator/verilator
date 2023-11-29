// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   logic[3:0] enable;
   int cyc = 0;

   Test test(.*);

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      `ifdef FAIL1 enable[0] <= 1; `endif
      enable[1] <= 1;
      `ifdef FAIL2 enable[2] <= 1; `endif
      enable[3] <= 1;
      if (cyc != 0) begin
         if (cyc == 10) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end
endmodule

module Test(
   input clk,
   input[3:0] enable
   );

   assert property (
     @(posedge clk iff enable[0])
     0
   ) else $stop;

   assert property (
     @(posedge clk iff enable[1])
     1
   );

   cover property (
     @(posedge clk iff enable[2])
     1
   ) $stop;

   cover property (
     @(posedge clk iff enable[3])
     0
   ) $stop;

endmodule
