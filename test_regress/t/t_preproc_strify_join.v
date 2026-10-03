// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Antmicro
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

// Preserve the outer argument nesting across parameterized macros in stringification.
// verilog_format: off
`define BELOW_MAX(s_) ((s_) <= 2)
`define IDENTITY(x_) x_
`define rpt_fatal(MSG_, ID_) msg = {ID_, " ", MSG_};
`define CHECK(T_, MSG_="", SEV_=error, ID_="id") begin if (T_) ; else begin `rpt_``SEV_($sformatf("Check failed (%s) %s", `"T_`", MSG_), ID_) end end
`define CHECK_FATAL(T_, MSG_="", ID_="id") `CHECK(T_, MSG_, fatal, ID_)

`CHECK_FATAL(!((a_size) <= 2))
`CHECK_FATAL(!`BELOW_MAX(a_size))
`CHECK_FATAL(!`BELOW_MAX(a_size), "message, )", "tag")
`CHECK_FATAL(!`BELOW_MAX(`IDENTITY(a_size)), "nested", "tag")
`CHECK_FATAL(!`BELOW_MAX(a_size) && !`BELOW_MAX(other_size), "two macros", "tag")

`define STRING_ARG(x_) `"`IDENTITY(x_)`"
`define TAKE_ARGS(a_, b_, c_) received(a_, b_, c_)
`TAKE_ARGS(($sformatf("%s", `STRING_ARG(value))), "tail", 7)
// verilog_format: on
