// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

primitive t_gate(dout1, dout2, a, b, c);
output dout1, dout2;
input a, b, c;

    table
        x 0 1  :   1;
        0 ? 1  :   1;
        0 1 0  :   0;
        1 1 ?  :   1;
        1 0 0  :   0;
        0 0 0  :   1;

    endtable
endprimitive

module top (a, b, c, o1, o2);
    input a, b, c;
    output o1, o2;
    t_gate(o1, o2, a, b, c);
endmodule
