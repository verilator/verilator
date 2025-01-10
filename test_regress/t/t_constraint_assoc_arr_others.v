// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

// Enum-based associative array
typedef enum { RED, GREEN, YELLOW } color_t;

class AssocArrayEnum;
    rand bit [7:0] colors [color_t];
    constraint c1 { foreach (colors[i]) colors[i] == 4; }

    function new();
        colors[RED] = 8'd5;
        colors[GREEN] = 8'd10;
        colors[YELLOW] = 8'd15;
    endfunction

    function void self_check();
        foreach (colors[i]) begin
            if (colors[i] != 4) $stop;
        end
    endfunction
endclass

// Struct (packed) index associative array
typedef struct packed {
    bit [2:0] high;
    bit [1:0] low;
} PackedIndexType;

class AssocArrayPackedStruct;
    rand bit [31:0] data [PackedIndexType];
    constraint c2 { foreach (data[i]) data[i] == 100; }

    function new();
        PackedIndexType idx;
        idx.high = 3'd1;
        idx.low = 2'd1;
        data[idx] = 32'd50;
    endfunction

    function void self_check();
        foreach (data[i]) begin
            if (data[i] != 100) $stop;
        end
    endfunction
endclass

// Array (packed) index associative array
typedef logic [2:0][7:0] IndexArrayType;

class AssocArrayArrayIndex;
    rand bit [31:0] data [IndexArrayType];
    constraint c3 { foreach (data[i]) data[i] == 0; }

    function new();
        IndexArrayType idx;
        idx = 0;
        data[idx] = 32'd75;
    endfunction

    function void self_check();
        foreach (data[i]) begin
            if (data[i] != 0) $stop;
        end
    endfunction
endclass

module t_constraint_assoc_array_others;

    AssocArrayEnum enum_arr;
    AssocArrayPackedStruct packed_arr;
    AssocArrayArrayIndex array_arr;
    int success = 0;

    initial begin
        // Create instances of the classes
        enum_arr = new();
        packed_arr = new();
        array_arr = new();

        // Randomization and self-check
        success = enum_arr.randomize();
        if (success != 1) $stop;
        enum_arr.self_check();

        success = packed_arr.randomize();
        if (success != 1) $stop;
        packed_arr.self_check();

        success = array_arr.randomize();
        if (success != 1) $stop;
        array_arr.self_check();

        $write("*-* All Finished *-*");
        $finish;
    end
endmodule
