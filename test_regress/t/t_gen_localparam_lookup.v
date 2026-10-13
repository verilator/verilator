// DESCRIPTION: Verilator: Self-checking test for localparams inside loop generate blocks
//
// This file is part of Verilator.
// See LICENSE for details.

`define stop \$stop
`define checkd(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);
    localparam L = 10;

    genvar i;
    generate
        for (i = 0; i < 2; i = i + 1) begin : g
            localparam DEP = L + i;
        end
    endgenerate

    initial begin
        `checkd(g[0].DEP, 10);
        `checkd(g[1].DEP, 11);
        \$write("*-* All Covered *-*\n");
        \$finish;
    end
endmodule
