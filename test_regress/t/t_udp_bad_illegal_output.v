// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

primitive t_gate_comb(dout, a, b, c);
input a, b, c;
output dout;

    table
        r 0 1  : ?:  1;
        r ? 1  : ?:  1;
        r ? 0  : ?:  1;
        0 1 0  :  ?: 0;
        1 1 ?  :  ?: *;
        f r 0  :  ?: 0;
        0 0 0  :  ?: *;

    endtable
endprimitive

primitive t_gate_seq(dout, a, b, c);
input a, b, c;
output dout;

    table
        x 0 1  :   1;
        r ? 1  :   1;
        0 1 0  :   0;
        1 1 ?  :   *;
        1 0 0  :   0;
        0 0 0  :   *;

    endtable
endprimitive

module top (a, b, c, o1, o2);
    input a, b, c;
    output o1, o2;
    t_gate_comb(o1, a, b, c);
    t_gate_seq(o2, a, b, c);
endmodule
