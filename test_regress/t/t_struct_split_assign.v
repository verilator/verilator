// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
          clk
          );
    input clk;

    int cyc = 0;
    always_ff @(posedge clk) begin
        cyc <= cyc + 1;
        if (cyc == 2) begin
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end

    typedef struct packed {
        logic foo;
        int bar;
        logic baz;
    } struct_t;

    logic what_a;
    int what_b;
    logic what_d;

    always_comb begin
        what_a = '1;
        what_b = '1;
    end

`ifdef SPLIT_VAR
    struct_t the_struct /* verilator split_var */;
`else
    struct_t the_struct;
`endif

    always_comb begin
        the_struct.foo = what_a;
        the_struct.bar = what_b;
        what_d = the_struct.baz;
    end

    other
    the_other
       (.foo (the_struct.foo),
        .baz (the_struct.baz));
endmodule

module other
(
    input  logic foo,
    output logic baz
);
    always_comb baz = 1'b1;
endmodule
