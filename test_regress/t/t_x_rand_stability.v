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
    logic [31:0] added /* verilator public */;
`endif
    logic [31:0] unused;
    logic [31:0] uninitialized2;

    always @(posedge clk) begin
        x_assigned <= 'x;
        cyc <= cyc + 1;
        $display("rand = 0x%x", $random());
        if (cyc == 4) begin
            if (uninitialized == uninitialized2) $stop();
            $display("uninitialized = 0x%x", uninitialized);
            $display("x_assigned = 0x%x", x_assigned);
            $display("uninitialized2 = 0x%x", uninitialized2);
            $display("Last rand = 0x%x", $random());
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end

endmodule
