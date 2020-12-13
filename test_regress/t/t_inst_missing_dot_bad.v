// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Stefan Wallentowitz.
// SPDX-License-Identifier: CC0-1.0

module t;
   initial begin
      $display("a=", missing.a);
   end
   missing missing();  // Intentionally missing
endmodule
