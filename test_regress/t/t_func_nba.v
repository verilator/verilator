// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0


interface intf
(
    input logic clk
);
    logic       blargh /*verilator isolate_assignments*/;
    int data;
    modport sink (
        input   clk,
        output  blargh,
        input   data
    );
    modport source (
        input clk, blargh,
        output data
    );
endinterface

module sub
(
    intf.sink intf_a,
    intf.source  intf_b
);
    function automatic logic ident_func(logic arg);
        return arg;
    endfunction
    function automatic logic other_func();
    endfunction
    wire bar /* verilator public */;
    always_ff @(posedge intf_a.clk) begin
            intf_a.blargh <= '1;
            if (other_func()) begin
            end
            if (ident_func(intf_a.data[0])) begin
                intf_b.data <= '1;
                intf_a.blargh <= '0;
            end
    end
endmodule

module t();
    logic clk;
    intf intf_b (.*);
    intf intf_a (.*);
    sub the_sub (.*);

    initial begin
        clk = '0;
        #10;
        clk = ~clk;
        #10;
        if (!intf_a.blargh) $stop;
        clk = ~clk;
        intf_a.data = '1;
        #10;
        clk = ~clk;
        #10;
        clk = ~clk;
        #10;
        if (intf_a.blargh) $stop;
        clk = ~clk;
        #10;
            $write("*-* All Finished *-*\n");
            $finish;
    end
endmodule
