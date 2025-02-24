// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

// Long String index associative array
class AssocArrayString;
    rand int string_arr [string];

    constraint c {
        string_arr["a_very_long_string"] == 65;
    }
    function new();
        string_arr["a_very_long_string"] = 0;
    endfunction
endclass

class keyClass;
    int id;
    function new();
        id = 3;
    endfunction
endclass
// Class index associative array
class AssocArrayClass;
    rand bit [31:0] data [keyClass];
    keyClass cl;
    // constraint c4 { foreach (data[i]) data[i] > 0;} Unsupported index type for an associative array in an iterative constraint.
    constraint c1 { data[cl] > 0;} // Illegal index expression of unpacked type in constraint.
    function new();
        cl = new();
        data[cl] = 32'd77;
    endfunction
endclass

typedef struct {
    int a;
    int b;
} UnpackedIndexType;
// Struct (unpacked) index associative array
class AssocArrayUnpackedStruct;
    rand bit [31:0] data [UnpackedIndexType];
    constraint c2 { foreach (data[i]) data[i] < 100; } // Illegal non-integral expression in random constraint.

    function new();
        UnpackedIndexType idx;
        idx.a = 1;
        idx.b = 2;
        data[idx] = 32'd25;
    endfunction
endclass

// Array (unpacked) index associative array
typedef logic [2:0] IndexArrayType[3];
class AssocArrayArrayIndex;
    rand bit [31:0] data [IndexArrayType];
    constraint c3 { foreach (data[i]) data[i] > 0; }

    function new();
        IndexArrayType idx;
        for (int j = 0; j < 4; j++) begin
            idx[j] = 3'd0;
        end
        data[idx] = 32'd75;
    endfunction
endclass

module t_constraint_assoc_arr_bad;

    AssocArrayString test_str;
    AssocArrayClass test_cls;
    AssocArrayUnpackedStruct test_unp_struct;
    AssocArrayArrayIndex test_unp_arr;
    int success = 0;

    initial begin
        test_str = new();
        test_cls = new();
        test_unp_struct = new();
        test_unp_arr = new();

        success += test_str.randomize();
        success += test_cls.randomize();
        success += test_unp_struct.randomize();
        success += test_unp_arr.randomize();

        if(success != 4) $stop;

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
