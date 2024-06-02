// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Toru Niina.
// SPDX-License-Identifier: CC0-1.0

`ifdef TEST_VERBOSE
 `define WRITE_VERBOSE(msg) $write(msg)
`else
 `define WRITE_VERBOSE(msg)
`endif

`default_nettype none
`timescale 1ns/1ps

module t;

    localparam cycle = 1000.0 / 100.0;
    localparam halfcycle = 0.5 * cycle;

    logic clk = '0;

    import "DPI-C" context task tb_c_wait();

    export "DPI-C" task tb_sv_wait;
    task automatic tb_sv_wait(input int n);
        `WRITE_VERBOSE("tb_sv_wait start...\n");
        repeat(n) @(negedge clk);
        `WRITE_VERBOSE("tb_sv_wait done!\n");
    endtask

    always #halfcycle clk = ~clk;

    initial begin
        `WRITE_VERBOSE("test start\n");
        repeat(10) @(posedge clk);
        `WRITE_VERBOSE("calling tb_c_wait...\n");
        tb_c_wait();
        `WRITE_VERBOSE("tb_c_wait finish\n");
        repeat(10) @(posedge clk);
        $write("*-* All Finished *-*\n");
        $finish;
    end

    initial #(cycle*30) $stop; // timeout
endmodule
