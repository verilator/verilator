// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
  integer i = 0;
  initial begin
    fork
      i = 1;
    join_none
    if (i == 1) $stop;
    $finish;
  end
endmodule
