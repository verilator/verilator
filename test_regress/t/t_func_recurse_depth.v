// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 jalcim
// SPDX-License-Identifier: CC0-1.0

module t;

  // Recursive function that needs depth > 1000 to constant-fold
  function automatic int recurse_sum;
    input int i;
    if (i == 0) recurse_sum = 0;
    else recurse_sum = i + recurse_sum(i - 1);
  endfunction

  localparam int S1500 = recurse_sum(1500);

  initial begin
    if (S1500 !== 1125750) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
