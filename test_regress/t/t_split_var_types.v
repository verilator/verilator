// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
    // Inputs
    clk
    );
    input clk;

    // Test loop
    always @ (posedge clk) begin
        $write("*-* All Finished *-*\n");
        $finish;
    end

    sub the_sub (.data_out());

endmodule

module sub(
    output logic [31:0][15:0] data_out
);
    logic [31:0][15:0] data [8] /*verilator split_var*/;
    always begin
        data_out = data[7];
    end
endmodule
