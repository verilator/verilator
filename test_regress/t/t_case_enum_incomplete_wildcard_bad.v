// DESCRIPTION: Verilator: SystemVerilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

module t;
    t1 i_t1();
endmodule

module t1;

    enum logic [1:0] {
        S00 = 'b00,
        S01 = 'b01,
        S10 = 'b10,

        SX0 = 2'b?0,
        S0X = 'b0?
    } state;

    int v = 0;

    initial begin
        state = S10;
        unique case (state)
            S00: $stop;
            2'b01: $stop;
        endcase
        unique case (state)
            2'd2: $stop;
            2'd1: v++;
        endcase

        unique casez (state)
            S0X: $stop;
            2'b11: $stop;
        endcase

        case (state)
            S00: $stop;
            S01: v++;
            S10: $stop;
        endcase
    end
endmodule
