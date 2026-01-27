// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

package foo;
`ifdef TEST_DECLARE_STD
    class std;
        static int bar;
    endclass
`endif
endpackage

module t;
    int baz = foo::std::bar;
endmodule
