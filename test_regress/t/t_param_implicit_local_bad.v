// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0


module t;
    class NestedCls #(
        parameter A = 0
    );
        parameter B = 0;
    endclass

    NestedCls #(1, 2) cls;

    mod1  # ( 3, 4, 5 )   i_mod1 ();
    mod2  # ( 5, 12, 13 ) i_mod2 ();
    mod3  # ( 7, 24, 25 ) i_mod3 ();
    intf1 # ( 8, 15, 17 ) i_intf1 ();
    prgm1 # ( 9, 40, 41 ) i_prgm1 ();
endmodule

`define CHECK_PARAMS  if (A**2 + B**2 != C**2) $error("A**2 + B**2 != C**2")

module mod1 # (
    parameter A = 1, B = 1
);
    parameter C = 1;
    `CHECK_PARAMS;
endmodule

module mod2 ();
    parameter A = 1, B = 1, C = 1;
    `CHECK_PARAMS;
endmodule

module mod3 #() ();
    parameter A = 1, B = 1, C = 1;
    `CHECK_PARAMS;
endmodule

interface intf1 # (
    parameter A = 1, B = 1
);
    parameter C = 1;
    `CHECK_PARAMS;
endinterface

program prgm1 # (
    parameter A = 1, B = 1
);
    parameter C = 1;
    `CHECK_PARAMS;
endprogram
