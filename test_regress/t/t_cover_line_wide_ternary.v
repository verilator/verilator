// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface intf();
    logic foo;
    logic [31:0] bar;
    logic [127:0] baz;
endinterface

module t (/*AUTOARG*/
    // Inputs
    clk
    );

    input clk;

    integer cyc;
    initial cyc=1;

    intf intfs [2] ();
    intf intf_sel();

    always_comb begin
        intfs[0].bar = 123;
        intfs[1].bar = 456;
    end

    always @ (posedge clk) begin
        {intf_sel.foo, intf_sel.bar, intf_sel.baz} <=
            cyc[0] ?
            {intfs[1].foo, intfs[1].bar, intfs[1].baz} :
            {intfs[0].foo, intfs[0].bar, intfs[0].baz};
    end

    always @ (posedge clk) begin
        cyc <= cyc + 1;
        if (cyc==9) begin
            $display("bar = %0d", intf_sel.bar);
            if (intf_sel.bar != 123) $stop();
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end
endmodule
