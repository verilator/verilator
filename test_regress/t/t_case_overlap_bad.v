// DESCRIPTION: Verilator: SystemVerilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

module t;
    t1 i_t1();
endmodule

module t1;

    int v = 0;

    logic [2:0] state;

    initial begin
        state = 2;
        casez (state)
            3'b00?: $stop;
            3'b001, 3'b000: $stop;
            default;
        endcase
        casez (state)
            3'b111, 3'b0??: v++;
            3'b00?: $stop;
            default;
        endcase
    end
endmodule
