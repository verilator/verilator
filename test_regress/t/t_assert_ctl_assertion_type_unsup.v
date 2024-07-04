// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
   let OFF = 4;
   let CONCURRENT = 1;
   let UNIQUE = 32; // unique if and case violation

   initial begin
      $assertcontrol(OFF, CONCURRENT | UNIQUE);
   end
endmodule
