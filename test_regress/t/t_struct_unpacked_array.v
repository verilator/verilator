// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


typedef struct {
    logic a;
} Data_t;

module t (/*AUTOARG*/
    clk
);
    input clk;
    int cyc = 0;

    localparam int SIZE = 20;
    reg[$clog2(SIZE)-1 : 0] ptr;
    Data_t buffer[SIZE];
    Data_t out;
    reg out1;

    always_ff @( posedge clk ) begin
        int i;
        cyc <= cyc + 1;
        if (cyc == 0) begin
            for (i=0;i<SIZE;i=i+1) begin
                buffer[i].a <= 0;
            end
        end
        else begin
            ptr <= (ptr+1);
            out <= buffer[ptr];
            out1 <= buffer[ptr].a;
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end

endmodule
