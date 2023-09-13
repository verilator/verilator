// DESCRIPTION: Verilator: SystemVerilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

// Fix bug4464

module t;

    enum logic [1:0] {
        S00 = 'b00,
        S01 = 'b01,
        S10 = 'b10,

        S0X = 2'b0?,
        SX0 = 2'b?0
    } state;

    int v = 0;

    initial begin
        state = S00;
        unique case (state)
            S00: $stop;
            S01: v++;
            S10: $stop;
        endcase
        unique case (state)
            S00: $stop;
            default: v++; // default
        endcase
        unique case (state)
            2'd0: $stop;
            2'd1: v++;
            2'd2: $stop;
        endcase
        unique case (state)
            2'd0: $stop;
            2'd1: v++;
            2'd2: $stop;
            2'd3: $stop; // extra case
        endcase

        unique case (state) inside
            2'd0: $stop;
            2'd1: v++;
            [2'd2:2'd3]: $stop;
        endcase
        unique case (state) inside
            [S00:S10]: v++;
        endcase

        unique casez (state)
            S10: $stop;
            S0X: v++; // fully covered
        endcase
        unique casez (state)
            S10: $stop;
            S0X: v++;
            2'b11: $stop; // extra case
        endcase
        unique casez (state)
            S0X: v++;
            default: $stop;
        endcase

        case (state)
            S00: $stop;
            S01: v++;
            S10, 2'b11: $stop;
        endcase
    end
endmodule
