// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);
   initial begin
      $display(local::x);
      $finish;
   end
endmodule
