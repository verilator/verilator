// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define FOO foo
`define BAR bar
`define QUX qux
`define STRIFY `"`FOO``-```BAR``-```QUX```"

`define NESTED_STRIFY `"`STRIFY```"

`define EMPTY
`define EMPTY_STRIFY `"`EMPTY```"

`STRIFY
`NESTED_STRIFY
`EMPTY_STRIFY
