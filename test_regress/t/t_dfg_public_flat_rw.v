// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module unoptflat_process_split (
    input  logic ptr_empty,
    input  logic pop_en,
    output logic empty,
    output logic pop_qual
);
    always_comb begin
        empty = ptr_empty;
        pop_qual = pop_en && !empty;
    end
endmodule

module external_write_guard (
    input  logic ptr_empty,
    output logic old_empty
);
    logic [1:0] empty;

    // An external write to empty[1] before evaluation must be visible to old_empty.
    // verilator lint_off UNOPTFLAT
    always @* begin
        empty[0] = ptr_empty;
        old_empty = empty[1];
    end
    // verilator lint_on UNOPTFLAT
endmodule

module top (
    input  logic ptr_empty,
    output logic pop_qual,
    output logic old_empty
);
    logic empty;
    logic pop_en;

    always_comb begin
        pop_en = 1'b0;
        if (!empty) pop_en = 1'b1;
    end

    unoptflat_process_split u_fifo_ctrl (
        .ptr_empty(ptr_empty),
        .pop_en   (pop_en),
        .empty    (empty),
        .pop_qual (pop_qual)
    );

    external_write_guard u_external_write_guard (
        .ptr_empty(ptr_empty),
        .old_empty(old_empty)
    );
endmodule
