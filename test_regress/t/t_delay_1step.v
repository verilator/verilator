// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
  timeunit 10s; timeprecision 1s;

  initial begin
    #1;
    if ($time != 1) $stop;
    repeat (10) #1step;
    if ($time != 2) $stop;
    #10;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
