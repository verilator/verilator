// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop;
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

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
        `checkd(std::randomize(test.addr, test.data), 1);
        if (test.addr == test.old_addr && test.data == test.old_data) $stop;
        `checkd(test.data_x_4, test.old_data_x_4);

        // Test function-based randomization
        `checkd(run(), 1);
        `checkd(test.std_randomize(), 1);

        // Test array randomization with constraints
        `checkd(std::randomize(limit) with { foreach (limit[i]) { limit[i] < 32'd100;}}, 1);
        foreach (limit[i]) if (limit[i] >= 32'd100) $stop;

        `checkd(std::randomize(limit_7bits) with { foreach (limit_7bits[i]) { limit_7bits[i] < 7'd10;}}, 1);
        foreach (limit_7bits[i]) if (limit_7bits[i] >= 7'd10) $stop;

        `checkd(std::randomize(limit_15bits) with { foreach (limit_15bits[i]) { limit_15bits[i] < 15'd1000;}}, 1);
        foreach (limit_15bits[i]) if (limit_15bits[i] >= 15'd1000) $stop;

        `checkd(std::randomize(limit_31bits) with { foreach (limit_31bits[i]) { limit_31bits[i] < 31'd100000;}}, 1);
        foreach (limit_31bits[i]) if (limit_31bits[i] >= 31'd100000) $stop;

        `checkd(std::randomize(limit_63bits) with { foreach (limit_63bits[i]) { limit_63bits[i] < 63'd10000000000;}}, 1);
        foreach (limit_63bits[i]) if (limit_63bits[i] >= 63'd10000000000) $stop;

        `checkd(std::randomize(limit_95bits) with { foreach (limit_95bits[i]) { limit_95bits[i] < 95'd1000000000000;}}, 1);
        foreach (limit_95bits[i]) if (limit_95bits[i] >= 95'd1000000000000) $stop;

        foreach (limit_63bits[i]) begin
            `checkd(std::randomize(limit_63bits[i]) with { limit_63bits[i] >= 63'd50; limit_63bits[i] < 63'd100;}, 1);
            if ((limit_63bits[i] < 63'd50) || (limit_63bits[i] >= 63'd100)) `stop;
        end

        foreach (limit_95bits[i]) begin
            `checkd(std::randomize(limit_95bits[i]) with { limit_95bits[i] >= 95'd50; limit_95bits[i] < 95'd1000;}, 1);
            if (limit_95bits[i] < 95'd50 || limit_95bits[i] >= 95'd1000) $stop;
        end

        // Test mixed argument types (VarRef + MemberSel + ArraySel) with interdependent constraints
        `checkd(std::randomize(addr, test.addr, limit_31bits[0]) with {
            addr > 8'd10; addr < 8'd50;
            test.addr > addr; test.addr < 8'd100;
            limit_31bits[0] > 31'(test.addr); limit_31bits[0] < 31'd200;
        }, 1);
        if (addr <= 8'd10 || addr >= 8'd50) `stop;
        if (test.addr <= addr || test.addr >= 8'd100) `stop;
        if (limit_31bits[0] <= 31'(test.addr) || limit_31bits[0] >= 31'd200) `stop;

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
