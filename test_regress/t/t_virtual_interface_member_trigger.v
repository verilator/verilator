// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps

interface INTF;
    logic x;
    logic y;
    logic z;
    logic [7:0] data;
endinterface

class Dummy;
    virtual INTF vif;
    function new(virtual INTF vif);
        this.vif = vif;
    endfunction
    task write_data(logic [7:0] d);
        vif.data = d;
    endtask
endclass

module t_virtual_interface_member_trigger();
    // === Part 1: logic trigger false loop test ===
    logic s1, s2, src_val;
    INTF intf_loop();
    virtual INTF vif_loop;
    assign intf_loop.x = s1;
    assign intf_loop.y = src_val;
    assign intf_loop.z = !intf_loop.y;
    assign s2 = intf_loop.z;
    assign s1 = s2;

    // === Part 2: data transfer chain test ===
    logic [7:0] data;
    INTF intf_read();
    INTF intf_write();
    assign intf_read.data = data;
    assign data = intf_write.data;
    virtual INTF vif_read, vif_write;

    Dummy cl_1, cl_2;

    initial begin

        // Test 1: no false loop with member-level trigger
        #1ns;
        vif_loop = intf_loop;
        cl_1 = new(vif_loop);
        #1ns;
        src_val = 0;
        #1ns;
        if (!(cl_1.vif.x == 1 && cl_1.vif.y == 0 && cl_1.vif.z == 1 && s1 == 1 && s2 == 1)) $stop;

        // Test 2: write from module
        #1ns;
        vif_read = intf_read;
        vif_write = intf_write;
        #1ns;
        vif_write.data = 8'hA5;
        #1ns;
        if (vif_read.data !== 8'hA5) $stop;

        // Test 3: write from class
        #1ns;
        cl_2 = new(vif_write);
        #1ns;
        cl_2.write_data(8'hB7);
        #1ns;
        if (vif_read.data !== 8'hB7) $stop;

        #5ns;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
