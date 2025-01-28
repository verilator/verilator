// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class AssocArrayWarningTest;

    rand int string_arr [string];

    constraint c {
        string_arr["a_very_long_string"] == 65;
    }
    function new();
        string_arr["a_very_long_string"] = 0;
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
