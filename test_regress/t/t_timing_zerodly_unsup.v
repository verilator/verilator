// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
    event e;
    logic v = 0;
    initial #1 begin
        fork
            #0 if (v) $finish;
               else $stop;
        join_none
        ->e;
    end
    initial @e v = 1;
endmodule
