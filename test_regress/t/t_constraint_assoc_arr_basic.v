// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class AssocArrTest;

    rand int int_index_arr [int];
    rand int string_index_arr [string];

    // Constraints for both arrays
    constraint int_index_constraints {
        foreach (int_index_arr[i]) int_index_arr[i] inside {10, 20, 30, 40};
    }
    constraint string_index_constraints {
        string_index_arr["Alice"] == 35;
        string_index_arr["Bob"] inside {50, 60};
        string_index_arr["Charlie"] > 25;
    }

    // Constructor to initialize arrays
    function new();
        int_index_arr = '{1: 10, 2: 20, 3: 30};
        string_index_arr = '{"Alice": 25, "Bob": 50, "Charlie": 45};
    endfunction

    // Function to check and display the arrays
    function void check_and_display();

        foreach (int_index_arr[i]) begin
            $display("int_index_arr[%0d] = %0d", i, int_index_arr[i]);
            if (!(int_index_arr[i] inside {10, 20, 30, 40})) $stop;
        end

        foreach (string_index_arr[name]) begin
            $display("string_index_arr[%s] = %0d", name, string_index_arr[name]);
            if ((name == "Alice" && string_index_arr[name] != 35) ||
                (name == "Bob" && !(string_index_arr[name] inside {50, 60})) ||
                (name == "Charlie" && string_index_arr[name] <= 25)) $stop;
        end
    endfunction
endclass

module t_constraint_assoc_arr_basic;

    AssocArrTest test_obj;
    initial begin
        test_obj = new();
        if (!test_obj.randomize()) $stop;

        test_obj.check_and_display();
        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule
