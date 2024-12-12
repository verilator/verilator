// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0


class AssocArrayWarningTest;

    rand int bit_index_arr [bit[78:0]];
    rand int logic_index_arr [logic[64:0]];

    constraint c {
        bit_index_arr[79'd66] == 65;
        logic_index_arr[65'd3] == 70;
    }
    function new();
        bit_index_arr = '{79'd66:0};
        logic_index_arr = '{65'd3:0};
    endfunction

endclass

module t_constraint_assoc_arr_bad;

    AssocArrayWarningTest test_obj;

    initial begin
        test_obj = new();
        repeat(2) begin
            int success;
            success = test_obj.randomize();
            if (success != 1) $stop;
        end
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
