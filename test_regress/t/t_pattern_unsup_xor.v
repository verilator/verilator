// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for issue where assignment pattern with XOR caused segfault
module t;
    typedef struct {
        logic bit_field;
    } status_t;

    status_t status_reg = '{bit_field: 1'b0} ^ 1'b0;
endmodule