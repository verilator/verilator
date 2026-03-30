// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module leaf(
    input sel,
    output logic ready
);
    always @(sel)
        if ((sel == 1))
            ready = 1;
endmodule

interface iface(input clk);
    logic sel;
    logic ready;
endinterface

class C_noinst;
    virtual iface v;
    int idx = 0;

    task t_noinst();
        forever begin
            @(posedge v.clk);
            if (v.ready && v.sel) begin
            end
        end
    endtask
endclass

module t;
    logic clk;
    iface i(.clk(clk));

    leaf d(
        .sel(i.sel),
        .ready(i.ready)
    );

    initial #1 clk = ~clk;

    initial #10 $finish;
endmodule
