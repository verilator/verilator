// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

// Test helper macros
`define ASSERT(expr) \
    if (!(expr)) begin \
        $display("%%Error: Assertion failed at line %0d: %s", `__LINE__, `"expr`"); \
        $stop; \
    end

`define RAND_ARRAY_CHECK(array, max_val) \
    begin \
        int _success; \
        _success = std::randomize(array) with { foreach (array[i]) { array[i] < max_val;}}; \
        `ASSERT(_success == 1) \
        foreach (array[i]) `ASSERT(array[i] < max_val) \
    end

class std_randomize_class;

    rand bit [7:0] addr;
    rand bit [31:0] data;
    rand bit [63:0] data_x_4;

    bit [7:0] old_addr;
    bit [31:0] old_data;
    bit [63:0] old_data_x_4;

    function bit std_randomize();
        int success;
        bit valid;

        old_addr = addr;
        old_data = data;
        old_data_x_4 = data_x_4;

        success = std::randomize(addr, data);

        valid = (success == 1) && !(addr == old_addr || data == old_data) && data_x_4 == old_data_x_4;

        return valid;
    endfunction

endclass

module t_scope_std_randomize;
    bit [7:0] addr;
    bit [15:0] data;
    int limit[10];
    bit [6:0] limit_7bits[10];
    bit [14:0] limit_15bits[10];
    bit [30:0] limit_31bits[10];
    bit [62:0] limit_63bits[10];
    bit [94:0] limit_95bits[10];

    function bit run();
        int ready;
        int success;

        bit [7:0] old_addr;
        bit [15:0] old_data;
        int old_ready;

        old_addr = addr;
        old_data = data;
        old_ready = ready;
        success = randomize(addr, ready); // std::randomize
        if (success == 0) return 0;
        if (addr == old_addr && data != old_data && ready == old_ready) begin
            return 0;
        end
        return 1;
    endfunction

    std_randomize_class test;

    initial begin

        // Test class member randomization
        test = new();
        test.old_addr = test.addr;
        test.old_data = test.data;
        test.old_data_x_4 = test.data_x_4;
        `ASSERT(std::randomize(test.addr, test.data) == 1)
        `ASSERT(!(test.addr == test.old_addr || test.data == test.old_data))
        `ASSERT(test.data_x_4 == test.old_data_x_4)

        // Test function-based randomization
        `ASSERT(run())
        `ASSERT(test.std_randomize())

        // Test array randomization with constraints
        /* verilator lint_off WIDTHEXPAND */
        `RAND_ARRAY_CHECK(limit, 100)
        `RAND_ARRAY_CHECK(limit_7bits, 10)
        `RAND_ARRAY_CHECK(limit_15bits, 1000)
        `RAND_ARRAY_CHECK(limit_31bits, 100000)
        `RAND_ARRAY_CHECK(limit_63bits, 64'd10000000000)
        `RAND_ARRAY_CHECK(limit_95bits, 96'd1000000000000)
        /* verilator lint_on WIDTHEXPAND */

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
