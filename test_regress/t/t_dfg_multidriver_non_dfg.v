// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

`default_nettype none

module t(
    input  wire i,
    output wire o
);
    logic a;
    logic b;
    initial begin
        a = 1'd0;
        b = 1'd0;
    end
    assign a = ~i;
    assign b = a;
    assign o = b;
endmodule
