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
endinterface

class Dummy;
    virtual INTF vif;
    function new(virtual INTF vif);
        this.vif = vif;
    endfunction
endclass

module t_virtual_interface_member_trigger();
    logic s1, src_val;
    logic s2;

    INTF vintf();

    assign vintf.x = s1;
    assign vintf.y = src_val;
    assign vintf.z = !vintf.y;
    assign s2 = vintf.z;
    assign s1 = s2;

    Dummy d;

    initial begin
        d = new(vintf);
        #1ns;
        src_val = 0;
        #1ns;
        if (!(d.vif.x == 1 && d.vif.y == 0 && d.vif.z == 1 && s1 == 1 && s2 == 1)) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
