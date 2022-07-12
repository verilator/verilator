// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   test,
   // Inputs
   clk
   );
   input clk;

   output reg [5:0] test;
   parameter STATE1 = 6'b000001;
   parameter STATE2 = 6'b000010;
   parameter STATE3 = 6'b000100;
   parameter STATE4 = 6'b001000;
   parameter STATE5 = 6'b010000;
   parameter STATE6 = 6'b100000;

   always @(posedge clk) begin
      $display("Clocked");
      case (test)
        STATE1: test <= STATE2;
        STATE2: test <= STATE3;
        STATE3: test <= STATE4;
        STATE4: test <= STATE5;
        STATE5: test <= STATE6;
        default: test <= STATE1;
      endcase
   end

   int cyc;
   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
