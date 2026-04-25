// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

package pkg;
    class C #(parameter P = 0);
        typedef struct packed {
            bit [7:0] x;
        } my_t;

        mailbox #(my_t) mb = new();

        task run();
            my_t v;
            mb.get(v);
        endtask
    endclass
endpackage

module top;
    import pkg::*;

    initial begin
        C #(0) c0;
        C #(1) c1;
    end
endmodule
