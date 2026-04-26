// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    output logic [64:0] output_vec[257]
);

  assign output_vec = '{default: 1};

  initial $finish;

endmodule
