// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

package Foo;
endpackage

package Bar;
    static int baz;
endpackage

module t;
    int baz = Foo::Bar::baz;
endmodule
