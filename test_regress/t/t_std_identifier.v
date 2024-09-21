// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
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
