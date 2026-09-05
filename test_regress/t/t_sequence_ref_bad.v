// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  sequence s_one;
    1;
  endsequence

  initial begin
    @s_one;
    $display("got sequence");
    $finish;
  end

endmodule
