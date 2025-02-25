// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t ();
   reg PoweredUp;
   specify
      specparam tdevice_PU = 3e8;
   endspecify
   initial begin
      PoweredUp = 1'b0;
      #tdevice_PU PoweredUp = 1'b1;
   end
endmodule
