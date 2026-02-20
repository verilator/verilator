// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// Test that functional coverage is properly written to coverage database
// Checks that coverage.dat contains funccov entries with correct format

// Expected coverage database entries will contain:
// - Type "funccov"
// - Bin names ("low", "high")
// - Hierarchy ("cg.cp.low", "cg.cp.high")

module t (/*AUTOARG*/);
    logic [1:0] data;

    covergroup cg;
        cp: coverpoint data {
            bins low  = {2'b00};
            bins high = {2'b11};
        }
    endgroup

    cg cg_inst = new;

    initial begin
        // Sample both bins
        data = 2'b00;
        cg_inst.sample();

        data = 2'b11;
        cg_inst.sample();

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
