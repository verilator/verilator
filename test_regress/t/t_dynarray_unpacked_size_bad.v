// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  int fixed[3];
  int dynamic[];

  initial begin
    dynamic = new[2];
    fixed = dynamic;  // IEEE 1800-2023 7.6 requires matching sizes
    $display("%0d", fixed[0]);
    $stop;
  end

endmodule
