// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`ifdef TEST_VERBOSE
 `define WRITE_VERBOSE(args) $write args
`else
 `define WRITE_VERBOSE(args)
`endif

module t;
   logic clk = 0;
   always #3 clk = ~clk;

   logic flag_a;
   logic flag_b;
   always @(posedge clk)
   begin
      `WRITE_VERBOSE(("[%0t] b <= 0\n", $time));
      flag_b <= 1'b0;
      #2
      `WRITE_VERBOSE(("[%0t] a <= 1\n", $time));
      flag_a <= 1'b1;
      #2
      `WRITE_VERBOSE(("[%0t] b <= 1\n", $time));
      flag_b <= 1'b1;
   end
   always @(flag_a) if ($time > 0)
   begin
      #1
      `WRITE_VERBOSE(("[%0t] Checking if b == 0\n", $time));
      if (flag_b !== 1'b0) $stop;
      #2
      `WRITE_VERBOSE(("[%0t] Checking if b == 1\n", $time));
      if (flag_b !== 1'b1) $stop;
      #10
      $write("*-* All Finished *-*\n");
      $finish;
   end
   initial #20 $stop; // timeout
endmodule
