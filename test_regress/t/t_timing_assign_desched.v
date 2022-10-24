// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
  logic clk = 0;
  always #1 clk = ~clk;

  logic a = 0;
  assign #2 a = clk;

  always @a if ($time > 0) $stop;

  initial #100 begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
