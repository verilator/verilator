// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module other_sub (
    input wire clk,
    input wire      foo,
    output logic     [5:0] bar
);
    always_comb bar[0] = foo;
`ifndef NO_ASSERT
    assert property (@(posedge clk) (foo == bar[0]));
`endif
    always_ff @(posedge clk) bar[5:1] <= bar[4:0];
endmodule

interface intf
    (input wire clk);
endinterface

module sub (
    input logic clk
);
    for (genvar k = 0; k < 4; k++) begin
        logic     [5:0] bar;
        other_sub
        the_other_sub (
            .clk,
            .foo ('1),
            .bar
        );
    end
endmodule

module t (
    input clk
);

    int cyc = 0;
    always @ (posedge clk) begin
        cyc <= cyc + 1;
        if (cyc == 9) begin
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end
    sub the_sub (.*);
endmodule
