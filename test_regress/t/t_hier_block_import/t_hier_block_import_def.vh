// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2024 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// No include guards to validate if included once.

`define VALUE_A 32'h12345678
`define VALUE_B 32'h87654321

typedef struct packed {
    bit [31:0] PARAM_VALUE;
} param_t;
