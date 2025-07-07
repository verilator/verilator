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

        // $display("Before randomization: addr: %0d, data: %0d, data_x_4: %0d", old_addr, old_data, old_data_x_4);
        success = std::randomize(addr, data);
        // $display("addr: %0d, data: %0d, data_x_4: %0d", addr, data, data_x_4);

        valid = success && !(addr == old_addr || data == old_data) && data_x_4 == old_data_x_4;
        if (!valid) return 0;
        return 1;
    endfunction

endclass

module t_scope_std_randomize;
    bit [7:0] addr;
    bit [15:0] data;

    function bit run();
        int ready;
        bit success;

        bit [7:0] old_addr;
        bit [15:0] old_data;
        int old_ready;

        old_addr = addr;
        old_data = data;
        old_ready = ready;
        // $display("Before randomization: addr=%0h, data=%0h, ready=%0d", addr, data, ready);
        success = std::randomize(addr, ready);
        // $display("After: addr=%0h, data=%0h, ready=%0d", addr, data, ready);
        if (!success) return 0;
        if (addr == old_addr && data != old_data && ready == old_ready) begin
            // $display("Error: Randomization did not change any values.");
            return 0;
        end
        return 1;
    endfunction

    std_randomize_class test;

    initial begin
        bit ok;
        ok = run();
        // $display("ok=%0d", ok);
        if (!ok) $stop;
        ok = 0;
        ok = test.std_randomize();
        if (!ok) $stop;

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
