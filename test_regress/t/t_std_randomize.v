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
        bit ok = 0;
        int success;

        test = new();
        test.old_addr = test.addr;
        test.old_data = test.data;
        test.old_data_x_4 = test.data_x_4;
        success = std::randomize(test.addr, test.data);
        ok = (success == 1) && !(test.addr == test.old_addr || test.data == test.old_data) && test.data_x_4 == test.old_data_x_4;
        if (!ok) $stop;

        ok = 0;
        ok = run();
        if (!ok) $stop;
        ok = 0;
        ok = test.std_randomize();
        if (!ok) $stop;
        /* verilator lint_off WIDTHEXPAND */
        success = std::randomize(limit) with { foreach (limit[i]) { limit[i] < 100;}};
        foreach (limit[i]) begin
            ok = (success == 1) && (limit[i] < 100);
            if (!ok) $stop;
        end
        success = std::randomize(limit_7bits) with { foreach (limit_7bits[i]) { limit_7bits[i] < 10;}};
        foreach (limit_7bits[i]) begin
            ok = (success == 1) && (limit_7bits[i] < 10);
            if (!ok) $stop;
        end
        success = std::randomize(limit_15bits) with { foreach (limit_15bits[i]) { limit_15bits[i] < 1000;}};
        foreach (limit_15bits[i]) begin
            ok = (success == 1) && (limit_15bits[i] < 1000);
            if (!ok) $stop;
        end
        success = std::randomize(limit_31bits) with { foreach (limit_31bits[i]) { limit_31bits[i] < 100000;}};
        foreach (limit_31bits[i]) begin
            ok = (success == 1) && (limit_31bits[i] < 100000);
            if (!ok) $stop;
        end
        success = std::randomize(limit_63bits) with { foreach (limit_63bits[i]) { limit_63bits[i] < 10000000000;}};
        foreach (limit_63bits[i]) begin
            ok = (success == 1) && (limit_63bits[i] < 10000000000);
            if (!ok) $stop;
        end
        success = std::randomize(limit_95bits) with { foreach (limit_95bits[i]) { limit_95bits[i] < 1000000000000;}};
        foreach (limit_95bits[i]) begin
            ok = (success == 1) && (limit_95bits[i] < 1000000000000);
            if (!ok) $stop;
        end
        /* verilator lint_off WIDTHEXPAND */
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
