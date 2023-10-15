// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

module sub();
endmodule

interface axi_stream_if #(
    parameter int  DATA_WIDTH = 64,
    parameter type TUSER_TYPE = logic
) (
    input clk
);

    task mytask();
    endtask : mytask

    genvar my_genvar;

    logic tvalid;

    sub i_sub();

    localparam PACKED_DATA_WIDTH = DATA_WIDTH + DATA_WIDTH / 8 + 1 + $bits(TUSER_TYPE);
endinterface

module t;
    logic clk;

    // overriding a localparam
    axi_stream_if # (.PACKED_DATA_WIDTH(10)) axis1(clk);
    // overriding a non-var
    axi_stream_if # (.mytask(10)) axis2(clk);
    // overriding a non-port/interface/param var
    axi_stream_if # (.my_genvar(10)) axis3(clk);
    // overriding a port
    axi_stream_if # (.clk(10)) axis4(clk);
    // overriding a signal
    axi_stream_if # (.tvalid(10)) axis5(clk);
    // overriding an instance
    axi_stream_if # (.i_sub(10)) axis6(clk);

endmodule
