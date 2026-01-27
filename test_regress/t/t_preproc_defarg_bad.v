// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2010 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

//See bug289

`define A1(x)
`define A2(x,y)

`A1
`A1(1,2)
`A2
`A2(1)
`A2(1,2,3)

module t;
endmodule
