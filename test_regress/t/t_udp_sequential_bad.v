// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

primitive or_gate(dout, a, b, c);
output dout;
input a, b, c;
reg dout;

    table
        x 0 1  :   1;
        0 ? 1  :   1;
        0 1 0  :   0;
        1 1 ?  :   1;
        1 0 0  :   0;
        0 0 0  :   1;

    endtable
endprimitive
module top (a, b, c, o);
    input a, b, c;
    output o;
    or_gate(o, a, b, c);
endmodule
