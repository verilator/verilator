// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    output wire out
);

    logic a = 1'b0;   // declaration initialization
    assign a = 1'b1;  // continuous assignment

    assign out = a;

endmodule
