// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Dan Petrisko
// SPDX-License-Identifier: CC0-1.0

module test_rom #(parameter filename_p);

    logic [3:0] mem [0:0];
    initial begin
        $readmemb(filename_p, mem);
        if (mem[0][0] != 1'b1) $stop;
        if (mem[0][1] != 1'b0) $stop;
        if (mem[0][2] != 1'b1) $stop;
        if (mem[0][3] != 1'b0) $stop;
    end

endmodule

module Test;

    // %Warning: $readmem file not found
    localparam string str_trace_file_lp = "t/t_readmemstr.mem";
    test_rom #(.filename_p(str_trace_file_lp)) str_rom();

    // Successfully finds file
    localparam def_trace_file_lp = "t/t_readmemstr.mem";
    test_rom #(.filename_p(def_trace_file_lp)) def_rom();

    initial begin
        #1000;
        $finish;
    end

endmodule

