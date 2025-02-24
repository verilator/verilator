// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 Krzysztof Boronski.
// SPDX-License-Identifier: CC0-1.0

int i = 0;

function int postincrement_i;
    return i++;
endfunction

module t;
    initial begin
        int arr [3][3] = {{1, 2, 3}, {4, 5, 6}, {7, 8, 9}};
        i = 0;
        arr[postincrement_i()][postincrement_i()]++;
        $display("Value: %d", i);
    end
endmodule
