// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

    localparam MXP_IB_SIZE_PARAM = 2;

    typedef struct packed {
        logic [MXP_IB_SIZE_PARAM-1:0] valid_m2_q;
        logic [MXP_IB_SIZE_PARAM-1:0] wptr_m1;
    } ib_t;

    ib_t ib;
    integer jj;

    logic reset_n = 0;
    logic set_valid0 = 0;
    integer cyc = 0;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            ib.valid_m2_q <= '0;
        else if (set_valid0)
            ib.valid_m2_q[0] <= 1'b1;
    end

    always @* begin : ff_avail
        ib.wptr_m1 = '0;

        for (jj = 0; jj < MXP_IB_SIZE_PARAM; jj = jj + 1) begin
            if (!ib.valid_m2_q[jj]) begin
                ib.wptr_m1[jj] = 1'b1;
                disable ff_avail;
            end
        end
    end

    always @(posedge clk) begin
        cyc <= cyc + 1;

        case (cyc)
            0: begin
                reset_n <= 1'b0;
            end
            1: begin
                reset_n <= 1'b1;
                set_valid0 <= 1'b1;
            end
            2: begin
                set_valid0 <= 1'b0;
            end
            3: begin
                if (ib.valid_m2_q != 2'b01)
                    $stop;
                if (ib.wptr_m1 != 2'b10)
                    $stop;

                $write("*-* All Finished *-*\n");
                $finish;
            end
        endcase
    end

endmodule
