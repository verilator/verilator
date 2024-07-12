// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Liam Braun.
// SPDX-License-Identifier: CC0-1.0

class cls #(
    parameter int ClsParam = 0
);
endclass

module submod #(
    parameter int ModParam
) ();
    cls #(
        .ClsParam(42)
    ) cls_inst;
endmodule;

module top ();
    submod #(
        .ModParam(42)
    ) i_submod ();
endmodule
