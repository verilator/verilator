// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    #0;
    #0;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
