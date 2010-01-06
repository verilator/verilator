// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

`timescale 1ns/1ns

module t;
   initial begin
      // Display formatting
      $write;  // Check missing arguments work
      $write("default:   [%0t] 0t time [%t] No0 time\n",$time,$time);
`ifndef verilator // Unsupported
      $timeformat(-9, 0, "",   0);
      $write("-9,0,,0:   [%0t] 0t time [%t] No0 time\n",$time,$time);
      $timeformat(-9, 0, "",   10);
      $write("-9,0,,10:  [%0t] 0t time [%t] No0 time\n",$time,$time);
      $timeformat(-9, 0, "ns", 5);
      $write("-9,0,ns,5: [%0t] 0t time [%t] No0 time\n",$time,$time);
      $timeformat(-9, 3, "ns", 8);
      $write("-9,3,ns,8: [%0t] 0t time [%t] No0 time\n",$time,$time);
`endif
      $write("\n");
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
