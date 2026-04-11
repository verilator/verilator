// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module Sub #(
    parameter int data_width
)(
    input clk,
    output logic [data_width-1:0]       read_data
);
    logic [0:0][data_width-1:0] read_data_2d;
    always_ff @(posedge clk) read_data_2d <= $random;
    always_comb read_data = read_data_2d[0];
endmodule

module t ();
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
        logic [7:0] field_c;
        logic field_d;
        logic field_e;
        logic field_f;
        logic field_g;
        logic field_h;
        logic field_i;
        logic field_j;
        logic field_k;
    } struct_t;
    struct_t the_struct;
    logic clk;

    Sub #(
        .data_width   ($bits(struct_t))
    ) the_sub(
        .clk,
        .read_data (the_struct)
    );

    initial begin
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
