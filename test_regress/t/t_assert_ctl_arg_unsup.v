// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
   let OFF = 4;
   let EXPECT = 16;
   let UNIQUE = 32;
   let UNIQUE0 = 64;
   let PRIORITY = 128;

   initial begin
      $assertcontrol(OFF, EXPECT);
      $assertcontrol(OFF, UNIQUE);
      $assertcontrol(OFF, UNIQUE0);
      $assertcontrol(OFF, PRIORITY);
   end
endmodule
