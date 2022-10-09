// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t(/*AUTOARG*/);
   int sig;
   initial begin
      sig = 10;
      $dumpfile({`STRINGIFY(`TEST_OBJ_DIR),"/simx.vcd"});
      $dumpvars();
      #20;
      sig = 20;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
