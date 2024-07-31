// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define foo test
`define a x,y
`define bar(a, b) test a b
`define baz(a, b) test``a``b
`define qux(x) string boo = x;
`define quux(x) `qux(`"x`")
`quux(`foo)
`quux(`bar(`a,`a))
`quux(`baz(`a,`bar(x,`a)))
`quux(`baz(`bar(`a,x), quux(`foo)))
