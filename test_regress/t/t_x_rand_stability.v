// DESCRIPTION: Verilator: Confirm x randomization stability
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


module t (/*AUTOARG*/
    // Inputs
    clk
    );

    input clk;
    int cyc = 0;

    logic [31:0] uninitialized;
    logic [31:0] x_assigned = '0;
`ifdef ADD_SIGNAL
    logic [31:0] added;
    logic [31:0] x_assigned_added = '0;
`endif
    logic [31:0] unused;
    logic [31:0] x_assigned_unused = '0;
    logic [31:0] uninitialized2;
    logic [255:0] big;
    int random_init = $random();

    sub_no_inline the_sub_no_inline_1();
    sub_no_inline the_sub_no_inline_2();
    sub_yes_inline the_sub_yes_inline_1();
    sub_yes_inline the_sub_yes_inline_2();

    initial begin
        $display("uninitialized = 0x%x", uninitialized);
        $display("x_assigned (initial) = 0x%x", x_assigned);
        $display("uninitialized2 = 0x%x", uninitialized2);
        $display("big = 0x%x", big);
        $display("random_init = 0x%x", random_init);
    end

    always @(posedge clk) begin
        x_assigned_unused = 'x;
        x_assigned <= 'x;
`ifdef ADD_SIGNAL
        x_assigned_added <= 'x;
`endif
        cyc <= cyc + 1;
        $display("rand = 0x%x", $random());
        if (cyc == 4) begin
            $display("x_assigned = 0x%x", x_assigned);
`ifndef NOT_RAND
            if (uninitialized == uninitialized2) $stop();
            if (the_sub_yes_inline_1.no_init == the_sub_yes_inline_2.no_init) $stop();
            if (the_sub_no_inline_1.no_init == the_sub_no_inline_2.no_init) $stop();
`endif
`ifdef ADD_SIGNAL
            if (added == 0) $stop();
            if (x_assigned_added == 0) $stop();
`endif
            $display("Last rand = 0x%x", $random());
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end

endmodule

module sub_no_inline; /* verilator no_inline_module */
    logic [63:0] no_init;
    initial $display("%m no_init 0x%0x", no_init);
endmodule

module sub_yes_inline; /* verilator inline_module */
    logic [63:0] no_init;
    initial $display("%m no_init 0x%0x", no_init);
endmodule
