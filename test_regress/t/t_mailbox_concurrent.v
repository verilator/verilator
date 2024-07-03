// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Liam Braun.
// SPDX-License-Identifier: CC0-1.0

module t();
    mailbox #(int) m;

    task automatic test_get;
        int v;
        m.get(v);
        // Only one thread should be here at a time (mailbox empty)
        $display("mailbox read %0t", $time);
        #1;
        m.put(v);
    endtask

    task automatic test_put;
        int v;
        m.put(42);
        // Only one thread should be here at a time (mailbox full)
        $display("mailbox write %0t", $time);
        #1;
        m.get(v);
    endtask

    initial begin
        m = new(1);
        m.put(42);

        fork
            test_get();
            test_get();
            test_get();
        join

        m = new(1);

        fork
            test_put();
            test_put();
            test_put();
        join

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
