// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  int fixed[3];
  int queue[$];
  int dynamic[];

  initial begin
    queue = '{1, 2, 3};
    fixed = queue;  // Legal (IEEE 1800-2023 7.6), but unsupported
    dynamic = new[3];
    fixed = dynamic;  // Legal (IEEE 1800-2023 7.6), but unsupported
  end

endmodule
