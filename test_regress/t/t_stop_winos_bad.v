// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`line 7 "C:\\some\\windows\\path\\t_stop_winos_bad.v" 0

module t;
   localparam string FILENAME = `__FILE__;
   initial begin
      $write("Intentional stop\n");
      // Print length to make sure \\ counts as 1 character
      $write("Filename '%s'  Length = %0d\n", FILENAME, FILENAME.len());
      $stop;
   end
endmodule
