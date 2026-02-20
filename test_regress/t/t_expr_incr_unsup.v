// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// SPDX-FileCopyrightText: 2022 Krzysztof Boronski
// SPDX-License-Identifier: CC0-1.0

int i = 0;

function int postincrement_i;
    return i++;
endfunction

module t;
    initial begin
        automatic int arr [1:0] = {0, 0};
        i = 0;
        $display("Value: %d", arr[postincrement_i()]++);
    end
endmodule
