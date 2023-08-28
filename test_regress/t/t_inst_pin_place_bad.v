// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

module sub # (
    parameter PARAM_A = 1,
    parameter type PARAM_B = logic
) (
    input pin_1
);
endmodule

module t;
    parameter type PARAM_B = string;

    sub #(
        .PARAM_B(PARAM_B),
        .pin_1(1)
    ) i_sub (
        .PARAM_A(1)
    );
endmodule
