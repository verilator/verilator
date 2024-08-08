// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
   logic clk1 = 0, clk2 = 0, clk3 = 0, clk4 = 0;
   always #2 clk1 = ~clk1;
   assign #1 clk2 = clk1;
   assign #1 clk3 = clk2;
   assign #1 clk4 = clk3;

   int x = 0;
   int cyc = 0;

   always @(posedge clk1) begin
      if (x != 0) $stop;
`ifdef TEST_VERBOSE
      $display("[%0t] clk1 | x=%0d cyc=%0d", $realtime, x, cyc);
`endif
      @(posedge clk2);
`ifdef TEST_VERBOSE
      $display("[%0t] clk2 | x=%0d cyc=%0d", $realtime, x, cyc);
`endif
      x <= x + 1;
      cyc <= cyc + 1;
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   always @(posedge clk3) begin
`ifdef TEST_VERBOSE
      $display("[%0t] clk3 | x=%0d cyc=%0d", $realtime, x, cyc);
`endif
      @(posedge clk4);
`ifdef TEST_VERBOSE
      $display("[%0t] clk4 | x=%0d cyc=%0d", $realtime, x, cyc);
`endif
      x <= x - 1;
   end
endmodule
