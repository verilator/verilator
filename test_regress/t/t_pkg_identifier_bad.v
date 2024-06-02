// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

package foo;
endpackage

package bar;
    static int baz;
endpackage

module t;
    int baz = foo::bar::baz;
endmodule
