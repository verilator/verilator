// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

    typedef logic [3:0] foo_t;

    foo_t foo_s;

    assign bar_s = {foo_s, foo_s}.f1;

endmodule
