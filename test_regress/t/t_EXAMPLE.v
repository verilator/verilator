// DESCRIPTION: Verilator: Verilog Test module
//
// Use this file as a template for submitting bugs, etc.
// This module takes a single clock input, and should either
//      $write("*-* All Finished *-*\n");
//      $finish;
// on success, or $stop.
//
// The code as shown applies a random vector to the Test
// module, then calculates a CRC on the Test module's outputs.
//
// **If you do not wish for your code to be released to the public
// please note it here, otherwise:**
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 ____YOUR_NAME_HERE____.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   initial begin
      // verilator lint_off WIDTH
      parameter [3:0] val0 = 32'b000x;
      parameter [3:0] val1 = 32'b000z;
      parameter [3:0] val2 = 32'b00xz;
      parameter [3:0] val3 = 32'b0000;
      $display(":assert: (%d == 1)", $isunknown(val0));
      $display(":assert: (%d == 1)", $isunknown(val1));
      $display(":assert: (%d == 1)", $isunknown(val2));
      $display(":assert: (%d == 0)", $isunknown(val3));
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
