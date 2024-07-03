// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Liam Braun.
// SPDX-License-Identifier: CC0-1.0

module t();
    semaphore s;

    // Stand-in for a task that should only be run by one thread at a time
    task automatic exclusive_task;
        $display("%0t", $time);
        #1;
    endtask

    task automatic call_exclusive_task;
        s.get(1);
        exclusive_task();
        s.put(1);
    endtask

    initial begin
        s = new(1);
        fork
            call_exclusive_task();
            call_exclusive_task();
            call_exclusive_task();
            call_exclusive_task();
        join

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
