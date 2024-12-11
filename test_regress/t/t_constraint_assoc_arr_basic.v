// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class constrained_associative_array_basic;

    rand int int_index_arr [int];
    rand int string_index_arr [string];
    /* verilator lint_off SIDEEFFECT */
    // Constraints for both arrays
    constraint int_index_constraints {
        foreach (int_index_arr[i]) int_index_arr[i] inside {10, 20, 30, 40, 50};
    }
    constraint string_index_constraints {
        string_index_arr["Alice"] == 35;
        string_index_arr["Bob"] inside {50, 60};
        string_index_arr["Charlie"] > 25;
    }

    // Constructor to initialize arrays
    function new();
        int_index_arr = '{1: 0, 8: 0, 7: 0};
        string_index_arr = '{"Alice": 25, "Bob": 50, "Charlie": 45};
    endfunction

    // Function to check and display the arrays
    function void self_check();
        foreach (int_index_arr[i]) begin
            if (!(int_index_arr[i] inside {10, 20, 30, 40, 50})) $stop;
        end
        foreach (string_index_arr[name]) begin
            if ((name == "Alice" && string_index_arr[name] != 35) ||
                (name == "Bob" && !(string_index_arr[name] inside {50, 60})) ||
                (name == "Charlie" && string_index_arr[name] <= 25)) $stop;
        end
    endfunction

endclass

class constrained_1d_associative_array;

    rand int string_index_arr [string];
    rand int int_index_arr [int];
    rand int shortint_index_arr [shortint];
    rand int longint_index_arr[longint];
    rand int byte_index_arr [byte];
    rand int bit_index_arr [bit[5:0]];
    rand int logic_index_arr [logic[3:0]];
    rand int bit_index_arr_1 [bit[55:0]];

    // Constraints
    constraint associative_array_constraints {
        string_index_arr["key1"] == 100;
        string_index_arr["key2"] inside {200, 300, 400};
        int_index_arr[40000] + int_index_arr[2000000000] == 2;
        shortint_index_arr[2000] == 200;
        longint_index_arr[64'd4000000000] == 300;
        byte_index_arr[8'd255] == 50;
        bit_index_arr[6'd30] - bit_index_arr_1[56'd66] == 3;
        logic_index_arr[4'b0011] == 70;
    }

    function new();
        string_index_arr = '{"key1":0, "key2":0};
        int_index_arr = '{40000:0, 2000000000:0};
        shortint_index_arr = '{2000:0};
        longint_index_arr = '{64'd4000000000:0};
        byte_index_arr = '{8'd255:0};
        bit_index_arr = '{6'd30:0};
        bit_index_arr_1 = '{56'd66:0};
        logic_index_arr = '{4'd3:0};
    endfunction

    function void self_check();
        if (string_index_arr["key1"] != 100) $stop;
        if (!(string_index_arr["key2"] inside {200, 300, 400})) $stop;
        if ((int_index_arr[40000] + int_index_arr[2000000000]) != 2) $stop;
        if (shortint_index_arr[2000] != 200) $stop;
        if (longint_index_arr[64'd4000000000] != 300) $stop;
        if (byte_index_arr[8'd255] != 50) $stop;
        if (bit_index_arr[6'd30] - bit_index_arr_1[56'd66] != 3) $stop;
        if (logic_index_arr[4'd3] != 70) $stop;
    endfunction

    function void debug_display();
        $display("string_index_arr[\"key1\"] = %0d", string_index_arr["key1"]);
        $display("string_index_arr[\"key2\"] = %0d", string_index_arr["key2"]);
        $display("int_index_arr[40000] = %0d", int_index_arr[40000]);
        $display("int_index_arr[2000000000] = %0d", int_index_arr[2000000000]);
        $display("shortint_index_arr[2000] = %0d", shortint_index_arr[2000]);
        $display("longint_index_arr[4000000000] = %0d", longint_index_arr[64'd4000000000]);
        $display("byte_index_arr[255] = %0d", byte_index_arr[8'd255]);
        $display("bit_index_arr[30] = %0d", bit_index_arr[6'd30]);
        $display("bit_index_arr_1[66] = %0d", bit_index_arr_1[56'd66]);
        $display("logic_index_arr[3] = %0d", logic_index_arr[4'd3]);
    endfunction

endclass

class constrained_2d_associative_array;

    rand int string_int_index_arr [string][int];
    rand int int_bit_index_arr [int][bit[5:0]];
    rand int string_bit_index_arr [string][bit[7:0]];
    rand int unpacked_assoc_array_2d [string][2];

    // Constraints
    constraint associative_array_constraints {
        string_int_index_arr["key1"][2000] == 100;
        string_int_index_arr["key2"][3000] inside {200, 300, 400};
        int_bit_index_arr[40000][6'd30] == 60;
        int_bit_index_arr[50000][6'd40] inside {100, 200};
        string_bit_index_arr["key3"][8'd100] == 150;
        string_bit_index_arr["key4"][8'd200] inside {250, 350};
        unpacked_assoc_array_2d["key5"][0] == 7;
    }

    function new();
        string_int_index_arr = '{"key1":'{2000:0}, "key2":'{3000:0}};
        int_bit_index_arr = '{40000:'{6'd30:0}, 50000:'{6'd40:0}};
        string_bit_index_arr = '{"key3":'{8'd100:0}, "key4":'{8'd200:0}};
        unpacked_assoc_array_2d["key5"][0] = 0;
        unpacked_assoc_array_2d["key5"][1] = 0;
    endfunction

    function void self_check();
        if (string_int_index_arr["key1"][2000] != 100) $stop;
        if (!(string_int_index_arr["key2"][3000] inside {200, 300, 400})) $stop;
        if (int_bit_index_arr[40000][6'd30] != 60) $stop;
        if (!(int_bit_index_arr[50000][6'd40] inside {100, 200})) $stop;
        if (string_bit_index_arr["key3"][8'd100] != 150) $stop;
        if (!(string_bit_index_arr["key4"][8'd200] inside {250, 350})) $stop;
        if (unpacked_assoc_array_2d["key5"][0] != 7) $stop;
    endfunction

    function void debug_display();
        $display("string_int_index_arr[\"key1\"][2000] = %0d", string_int_index_arr["key1"][2000]);
        $display("string_int_index_arr[\"key2\"][3000] = %0d", string_int_index_arr["key2"][3000]);
        $display("int_bit_index_arr[40000][30] = %0d", int_bit_index_arr[40000][6'd30]);
        $display("int_bit_index_arr[50000][40] = %0d", int_bit_index_arr[50000][6'd40]);
        $display("string_bit_index_arr[\"key3\"][100] = %0d", string_bit_index_arr["key3"][8'd100]);
        $display("string_bit_index_arr[\"key4\"][200] = %0d", string_bit_index_arr["key4"][8'd200]);
        $display("unpacked_assoc_array_2d[\"key5\"][0] = %0d", unpacked_assoc_array_2d["key5"][0]);
    endfunction
    /* verilator lint_off SIDEEFFECT */
endclass

module t_constraint_assoc_arr_basic;

    constrained_associative_array_basic my_array;
    constrained_1d_associative_array my_1d_array;
    constrained_2d_associative_array my_2d_array;
    int success;

    initial begin
        my_array = new();
        success = my_array.randomize();
        if (success == 0) $stop;
        my_array.self_check();

        my_1d_array = new();
        success = my_1d_array.randomize();
        if (success == 0) $stop;
        my_1d_array.self_check();

        my_1d_array = new();
        success = my_1d_array.randomize();
        if (success == 0) $stop;
        my_1d_array.self_check();

        // my_1d_array.debug_display();
        // my_2d_array.debug_display();

        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule
