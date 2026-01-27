// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`begin_keywords "1800-2023"

`define ONE
`undef ZERO

`elsif ( ONE )  // BAD: elsif without if
`endif

`ifdef ( ) // BAD: Missing value
`endif

`ifdef ( && ZERO)  // BAD: Expr
`endif

`ifdef ( ZERO && )  // BAD: Expr
`endif

`ifdef ( 1 )  // BAD: Constant
`endif

`ifdef ( ONE & ZERO)  // BAD: Operator
`endif

`ifdef ( % )  // BAD: % is syntax error
`endif

`ifdef ) // BAD: ) without (
`endif

`ifdef ( ONE // BAD: Missing paren
`endif
