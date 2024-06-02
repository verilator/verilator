// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// bug3806

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   reg [3:0]  in;
   tri [3:0]  bus = in;

   int        never_driven;
   int        never_forced;

   task force_bus;
      force bus[1:0] = 2'b10;
   endtask

   task release_bus;
      release bus;
   endtask

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         in <= 4'b0101;
      end
      else if (cyc == 10) begin
         $display("10");
      end
      else if (cyc == 11) begin
         $display("11");
      end
      //
      // bus
      else if (cyc == 10) begin  // Should warn
         $display("10b");
      end
      else if (cyc == 11) begin  // Should warn
         $display("11b");
      end
      //
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
