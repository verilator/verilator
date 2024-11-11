// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

package Foo;
endpackage

package Bar;
    static int baz;
endpackage

module t;
    int baz = Foo::Bar::baz;
endmodule
