// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps

interface INTF();
    logic clk;
    logic [7:0] data;
    logic valid;
    logic ready;
endinterface

time TA = 5ns;

class intf_driver;
    virtual INTF intf;
    function new(virtual INTF intf);
        this.intf = intf;
    endfunction

    task cycle_start();
        #TA;
    endtask

    task cycle_end();
        @(posedge intf.clk);
    endtask

    task init_master();
        intf.data = '0;
        intf.valid = 0;
    endtask

    task init_slave();
        intf.ready = 0;
    endtask

    task recv_data(output logic [7:0] data);
        intf.ready <= #TA 1;
        cycle_start();
        while (!(intf.valid && intf.ready)) begin cycle_end(); cycle_start(); end
        cycle_end();
        data = intf.data;
        intf.ready <= #TA 0;
    endtask

    task send_data(input logic [7:0] data);
        intf.data <= #TA data;
        intf.valid <= #TA 1;
        cycle_start();
        while (!(intf.valid && intf.ready)) begin cycle_end(); cycle_start(); end
        cycle_end();
        intf.valid <= #TA 0;
    endtask
endclass

module t;
    logic clk;
    logic [7:0] data;
    logic valid;
    logic ready;
    logic [7:0] recv_data;

    INTF read_intf();
    assign read_intf.clk = clk;
    assign read_intf.data = data;
    assign read_intf.valid = valid;
    assign ready = read_intf.ready;

    INTF write_intf();
    assign write_intf.clk = clk;
    assign data = write_intf.data;
    assign valid = write_intf.valid;
    assign write_intf.ready = ready;

    intf_driver driver_master;
    intf_driver driver_slave;

    virtual INTF vif_read = read_intf;
    virtual INTF vif_write = write_intf;

    initial begin
        repeat(1000) begin
            clk = '1;
            #10ns;
            clk = '0;
            #10ns;
        end
    end

    initial begin
        driver_master = new(vif_write);
        driver_slave = new(vif_read);

        driver_master.init_master();
        driver_slave.init_slave();
        fork
            begin
                #35ns;
                driver_master.send_data(8'h42);
                // $display("[%0d]: Write data: %02x", $time, write_intf.data);
                #10ns;
                driver_master.send_data(8'h43);
                // $display("[%0d]: Write data: %02x", $time, write_intf.data);
                #10ns;
                driver_master.send_data(8'h44);
                // $display("[%0d]: Write data: %02x", $time, write_intf.data);
            end
            begin
                #10ns;
                driver_slave.recv_data(recv_data);
                // $display("[%0d]: Got data: %02x", $time, recv_data);
                if (recv_data !== 8'h42) $stop;
                #5ns;
                driver_slave.recv_data(recv_data);
                // $display("[%0d]: Got data: %02x", $time, recv_data);
                if (recv_data !== 8'h43) $stop;
                #15ns;
                driver_slave.recv_data(recv_data);
                // $display("[%0d]: Got data: %02x", $time, recv_data);
                if (recv_data !== 8'h44) $stop;
            end
        join

        $write("*-* All Finished *-*\n");
        $finish;
    end

    // Dump waveforms
    // initial begin
    //     $dumpfile("t_virtual_interface_member_trigger.vcd");
    //     $dumpvars(0, t_virtual_interface_member_trigger);
    // end

endmodule
