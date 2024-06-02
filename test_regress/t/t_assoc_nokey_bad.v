// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   initial begin
      int dict[string] = '{1, 2};
      int dict2[string] = '{3: 4};  // Legal due to value-to-string conversion
      $display("dict=%p", dict);
      $display("dict2=%p", dict2);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
