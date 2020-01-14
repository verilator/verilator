// DESCRIPTION: Verilator: Verilog Test module for display/write padding.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Pieter Kapsenberg.

module t;
integer n; initial n = 23;
    initial begin
        $write("%0d %2d %8d\n", 23, 23, 23);
        $write("%-0d %-2d %-8d\n", 23, 23, 23);
        $write("%0d %2d %8d\n", n, n, n);
        $write("%-0d %-2d %-8d\n", n, n, n);
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
