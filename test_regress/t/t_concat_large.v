// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2015 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  reg [32767:0] a;

  initial begin
    a = {32768{1'b1}};
    if (a[32000] != 1'b1) $stop;
    a = '0;
    if (a[32000] != 1'b0) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
