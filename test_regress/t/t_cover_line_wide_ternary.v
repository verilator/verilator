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
    intf intf_sel_ff();
    intf intf_sel_comb();
    intf intf_sel_assign();

    always_comb begin
        intfs[0].bar = 123;
        intfs[1].bar = 456;
    end

    always_ff @ (posedge clk) begin
        {intf_sel_ff.foo, intf_sel_ff.bar, intf_sel_ff.baz} <=
            cyc[0] ?
            {intfs[1].foo, intfs[1].bar, intfs[1].baz} :
            {intfs[0].foo, intfs[0].bar, intfs[0].baz};
    end

    always_comb begin
        {intf_sel_comb.foo, intf_sel_comb.bar, intf_sel_comb.baz} =
            cyc[0] ?
            {intfs[1].foo, intfs[1].bar, intfs[1].baz} :
            {intfs[0].foo, intfs[0].bar, intfs[0].baz};
    end

    assign
        {intf_sel_assign.foo, intf_sel_assign.bar, intf_sel_assign.baz} =
            cyc[0] ?
            {intfs[1].foo, intfs[1].bar, intfs[1].baz} :
            {intfs[0].foo, intfs[0].bar, intfs[0].baz};

    always @ (posedge clk) begin
        cyc <= cyc + 1;
        if (cyc==9) begin
            if (intf_sel_ff.bar != 123) $stop();
            if (intf_sel_comb.bar != 456) $stop();
            if (intf_sel_assign.bar != 456) $stop();
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end
endmodule
