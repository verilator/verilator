// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
    bit [7:0] byte_value;
    int int_value;
} PackedStruct;

typedef struct {
    rand bit [7:0] byte_value;
    rand int int_value;
    int non_rand_value;  // Non-randomized member
} UnpackedStruct;

class PackedStructTest;
    rand PackedStruct packed_struct;

    function new();
        packed_struct.byte_value = 8'hA0;
        packed_struct.int_value = 0;
    endfunction

    // Constraint block for packed struct
    constraint packed_struct_constraint {
        packed_struct.byte_value == 8'hA0;
        packed_struct.int_value inside {[0:100]};
    }

    // Self-check function for packed struct
    function void check();
        if (packed_struct.byte_value != 8'hA0) $stop;
        if (!(packed_struct.int_value inside {[0:100]})) $stop;
    endfunction
endclass

class UnpackedStructTest;
    rand UnpackedStruct unpacked_struct;

    function new();
        unpacked_struct.byte_value = 8'h00;
        unpacked_struct.int_value = 0;
        unpacked_struct.non_rand_value = 42;  
    endfunction

    // Constraint block for unpacked struct
    constraint unpacked_struct_constraint {
        unpacked_struct.byte_value inside {8'hA0, 8'hB0, 8'hC0};
        unpacked_struct.int_value inside {[50:150]};
    }

    // Self-check function for unpacked struct
    function void check();
        if (!(unpacked_struct.byte_value inside {8'hA0, 8'hB0, 8'hC0})) $stop;
        if (!(unpacked_struct.int_value inside {[50:150]})) $stop;
        if (unpacked_struct.non_rand_value != 42) $stop;  // Check non-randomized member
    endfunction
endclass

module t_constraint_struct;
    PackedStructTest packed_struct_test;
    UnpackedStructTest unpacked_struct_test;
    int success;

    initial begin
        // Test packed struct
        packed_struct_test = new();
        repeat(10) begin
            success = packed_struct_test.randomize();
            if (success == 0) $stop;
            packed_struct_test.check();  // Self-check for packed struct
        end

        // Test unpacked struct
        unpacked_struct_test = new();
        repeat(10) begin
            success = unpacked_struct_test.randomize();
            if (success == 0) $stop;
            unpacked_struct_test.check();  // Self-check for unpacked struct
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
