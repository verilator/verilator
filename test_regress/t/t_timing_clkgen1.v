// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module clkgen(output bit clk);
   initial begin
      #(8.0:5:3) clk = 1;  // Middle is default
      forever begin
         #5 clk = ~clk;
      end
   end
endmodule

module t(/*AUTOARG*/);
   wire logic clk;

   clkgen clkgen (.clk);

   int  cyc;
   always @ (posedge clk) begin
      cyc <= cyc + 1;
`ifdef TEST_VERBOSE
      $display("[%0t] cyc=%0d", $time, cyc);
`endif
      if (cyc == 0) begin
         if ($time != 5) $stop;
      end
      else if (cyc == 1) begin
         if ($time != 15) $stop;
      end
      else if (cyc == 2) begin
         if ($time != 25) $stop;
      end
      else if (cyc == 9) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
