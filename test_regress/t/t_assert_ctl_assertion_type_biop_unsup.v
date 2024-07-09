// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
   let OFF = 4;
   let CONCURRENT = 1;
   let SIMPLE_IMMEDIATE = 2;
   let OBSERVED_DEFERRED_IMMEDIATE = 4;

   initial begin
      $assertcontrol(OFF, CONCURRENT | SIMPLE_IMMEDIATE | OBSERVED_DEFERRED_IMMEDIATE);
   end
endmodule
