// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class std_randomize_class;

    rand bit [7:0] addr;
    rand bit [31:0] data;
    rand bit [63:0] data_x_4;

    bit [7:0] old_addr;
    bit [31:0] old_data;
    bit [63:0] old_data_x_4;

    function int std_randomize();
        bit success, valid;

        old_addr = addr;
        old_data = data;
        old_data_x_4 = data_x_4;

        success = std::randomize(addr, data);

        valid = success && !(addr == old_addr || data == old_data) && data_x_4 == old_data_x_4;
        if (!valid) return 0;
        return 1;
    endfunction

endclass


module t_std_randomize_bad2;

    bit success, valid;
    std_randomize_class test;

    initial begin

        test = new();

        test.old_addr = test.addr;
        test.old_data = test.data;
        test.old_data_x_4 = test.data_x_4;
        success = std::randomize(test.addr, test.data);
        valid = success && !(test.addr == test.old_addr || test.data == test.old_data) && test.data_x_4 == test.old_data_x_4;

        // valid = test.std_randomize();

        if (!valid) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule : t_std_randomize_bad2
