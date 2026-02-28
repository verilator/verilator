// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Ethan Sifferman
// SPDX-License-Identifier: CC0-1.0

module DECLFILENAME;
    logic UNUSEDSIGNAL;
    logic [0:1] ASCRANGE_UNDRIVEN;
    always_comb begin
        case (ASCRANGE_UNDRIVEN)
            2'b0x: UNUSEDSIGNAL = 1;
        endcase
    end

`ifdef T_VLT_MATCH_ERROR_1
    import hi::*;
`elsif T_VLT_MATCH_ERROR_2
    initial $readmemh("", EC_ERROR);
`elsif T_VLT_MATCH_ERROR_3
    initial #1;
`endif
endmodule
