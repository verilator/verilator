// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic[3:0] D1, D2, Q1, Q2;
   always @(posedge clk) begin
       {Q1, Q2} <= {D1, D2};
   end

   always @(posedge clk) $display("[%0t] posedge clk", $time);

   clocking cb @(posedge clk);
      input #0 Q = {Q1, Q2};
      output #0 D = {D1, D2};
   endclocking

   initial $monitor("[%0t] --> D=%x\t\tQ=%x\t\tcb.Q=%x", $time, {D1,D2}, {Q1,Q2}, cb.Q);

   int cyc = 0;
   always @ (posedge clk) begin
       cyc <= cyc + 1;
       if (cyc > 1 && cb.Q != {D1 - 4'd1, D2 - 4'd1}) $stop;
       cb.D <= {D1 + 4'd1, D2 + 4'd1};
       if (cyc==10) begin
          $write("*-* All Finished *-*\n");
          $finish;
       end
   end
endmodule
