// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`ifdef WITH_DELAY
`define DELAY #1
`define TIME_AFTER_FIRST_WAIT 2
`define TIME_AFTER_SECOND_WAIT 3
`else
`define DELAY
`define TIME_AFTER_FIRST_WAIT 1
`define TIME_AFTER_SECOND_WAIT 1
`endif

class nba_waiter;
    // Task taken from UVM
    task wait_for_nba_region;
        int nba;
        int next_nba;
        next_nba++;
        nba <= `DELAY next_nba;
        @(nba);
    endtask
endclass

class Foo;
    task bar(logic a, logic b);
        int x;
        int y;
        // bar's local vars and intravals could be overwritten by other locals
        if (a) x <= `DELAY 'hDEAD;
        if (b) y <= `DELAY 'hBEEF;
        #2
        if (x != 'hDEAD) $stop;
    endtask

   task qux();
        int x[] = new[1];
        x[0] <= `DELAY 'hBEEF;  // Segfault check
    endtask
endclass

module t;
    nba_waiter waiter = new;
    Foo foo = new;
    event e;
    int cnt = 0;

    initial begin
        #1 ->e;
        if (cnt != 0) $stop;
        cnt++;
        waiter.wait_for_nba_region;
        ->e;
        if (cnt != 2) $stop;
        if ($time != `TIME_AFTER_FIRST_WAIT) $stop;
        cnt++;
        waiter.wait_for_nba_region;
        if (cnt != 4) $stop;
        if ($time != `TIME_AFTER_SECOND_WAIT) $stop;
        foo.bar(1, 1);
        foo.qux();
        #2
        $write("*-* All Finished *-*\n");
        $finish;
    end

    initial begin
        @e if (cnt != 1) $stop;
        cnt++;
        @e if (cnt != 3) $stop;
        cnt++;
    end
endmodule
