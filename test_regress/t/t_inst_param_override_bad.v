// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

interface axi_stream_if #(
    parameter int  DATA_WIDTH = 64,
    parameter type TUSER_TYPE = logic
) (
    input clk
);

    task mytask();
    endtask : mytask

    genvar my_genvar;

    localparam PACKED_DATA_WIDTH = DATA_WIDTH + DATA_WIDTH / 8 + 1 + $bits(TUSER_TYPE);
endinterface

module t;
    logic clk;

    // overriding a localparam
    axi_stream_if # (.PACKED_DATA_WIDTH(14)) axis1(clk);
    // overriding a non-var
    axi_stream_if # (.mytask(14)) axis2(clk);
    // overriding a non-port/interface/param var
    axi_stream_if # (.my_genvar(14)) axis3(clk);

endmodule
