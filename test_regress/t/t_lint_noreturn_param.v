// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  // verilator lint_off UNDRIVEN

  function integer log2m1();  // <--- Warning: No return
  endfunction

  localparam WIDTH = log2m1();

  initial begin
    if (WIDTH !== {32{1'bx}}) $stop;
    $finish;
  end

endmodule
