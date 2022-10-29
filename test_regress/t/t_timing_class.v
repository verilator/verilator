// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`ifdef TEST_VERBOSE
 `define WRITE_VERBOSE(args) $write args
`else
 `define WRITE_VERBOSE(args)
`endif

module t;
    // =============================================
    // EVENTS
    class EventClass;
        event e;
        int trig_count;

        function new;
            trig_count = 0;
        endfunction

        task inc_trig_count;
            trig_count++;
        endtask;

        task sleep;
            @e inc_trig_count;
            `WRITE_VERBOSE(("Event in class triggered at time %0t!\n", $time));
        endtask

        task wake;
            ->e;
        endtask
    endclass

    class WaitClass;
        int a;
        int b;
        logic ok;

        function new;
            a = 0;
            b = 0;
            ok = 0;
        endfunction

        task await;
            wait(a == 4 && b > 16) if (a != 4 || b <= 16) $stop;
            ok = 1;
            `WRITE_VERBOSE(("Condition in object met at time %0t!\n", $time));
        endtask
    endclass

    class LocalWaitClass;
        logic ok;

        function new;
            ok = 0;
        endfunction

        task await;
            int a = 0;
            int b = 100;
            fork
                wait(a == 42 || b != 100) if (a != 42 && b == 100) $stop;
                #10 a = 42;
            join
            ok = 1;
            `WRITE_VERBOSE(("Condition with local variables met at time %0t!\n", $time));
        endtask
    endclass

    EventClass ec = new;
    WaitClass wc = new;
    LocalWaitClass lc = new;

    initial begin
        @ec.e;
        ec.sleep;
        if (wc.ok) $stop;
        wc.await;
        if (lc.ok) $stop;
        lc.await;
    end

    initial #20 ec.wake;
    initial #40 ->ec.e;
    initial begin
        wc.a = #50 4;
        wc.b = #10 32;
    end

    always @ec.e begin
        ec.inc_trig_count;
        `WRITE_VERBOSE(("Event in class triggered at time %0t!\n", $time));
    end

    initial begin
        #80
        if (ec.trig_count != 3) $stop;
        if (!wc.ok) $stop;
        if (!lc.ok) $stop;
    end

    // =============================================
    // DELAYS
    virtual class DelayClass;
        pure virtual task do_delay;
        pure virtual task do_sth_else;
    endclass

    `ifdef TEST_VERBOSE
     `define DELAY_CLASS(dt) \
     class Delay``dt extends DelayClass; \
         virtual task do_delay; \
             $write("Starting a #%0d delay\n", dt); \
             #dt \
             $write("Ended a #%0d delay\n", dt); \
         endtask \
         virtual task do_sth_else; \
             $write("Task with no delay (in Delay%0d)\n", dt); \
         endtask \
     endclass
    `else
     `define DELAY_CLASS(dt) \
     class Delay``dt extends DelayClass; \
         virtual task do_delay; \
             #dt; \
         endtask \
         virtual task do_sth_else; \
         endtask \
     endclass
    `endif

    `DELAY_CLASS(10);
    `DELAY_CLASS(20);
    `DELAY_CLASS(40);

    class NoDelay extends DelayClass;
        virtual task do_delay;
            `WRITE_VERBOSE(("Task with no delay\n"));
        endtask
        virtual task do_sth_else;
            `WRITE_VERBOSE(("Task with no delay (in NoDelay)\n"));
        endtask
    endclass

    class AssignDelayClass;
        logic x;
        logic y;
        task do_assign;
            y = #10 x;
            `WRITE_VERBOSE(("Did assignment with delay\n"));
        endtask
    endclass

    initial begin
        DelayClass dc;
        Delay10 d10 = new;
        Delay20 d20 = new;
        Delay40 d40 = new;
        NoDelay dNo = new;
        AssignDelayClass dAsgn = new;
        `WRITE_VERBOSE(("I'm at time %0t\n", $time));
        dc = d10;
        dc.do_delay;
        dc.do_sth_else;
        `WRITE_VERBOSE(("I'm at time %0t\n", $time));
        if ($time != 10) $stop;
        dc = d20;
        dc.do_delay;
        dc.do_sth_else;
        `WRITE_VERBOSE(("I'm at time %0t\n", $time));
        if ($time != 30) $stop;
        dc = d40;
        dc.do_delay;
        dc.do_sth_else;
        `WRITE_VERBOSE(("I'm at time %0t\n", $time));
        if ($time != 70) $stop;
        dc = dNo;
        dc.do_delay;
        dc.do_sth_else;
        `WRITE_VERBOSE(("I'm at time %0t\n", $time));
        dAsgn.x = 1;
        dAsgn.y = 0;
        fork #5 dAsgn.x = 0; join_none
        dAsgn.do_assign;
        if ($time != 80) $stop;
        if (dAsgn.y != 1) $stop;
        // Test if the object is deleted before do_assign finishes:
        fork dAsgn.do_assign; join_none
        #5 dAsgn = null;
        #15 $write("*-* All Finished *-*\n");
        $finish;
    end

    // =============================================
    // FORKS
    class ForkDelayClass;
        task do_delay; #40; endtask
    endclass

    class ForkClass;
        int done = 0;
        task do_fork();
            ForkDelayClass d;
            fork
                begin
                    #10 done++;
                    `WRITE_VERBOSE(("Forked process %0d ending at time %0t\n", done, $time));
                end
                begin
                    #20 done++;
                    `WRITE_VERBOSE(("Forked process %0d ending at time %0t\n", done, $time));
                    d = new;
                end
                begin
                    #30 d.do_delay;
                    done++;
                    `WRITE_VERBOSE(("Forked process %0d ending at time %0t\n", done, $time));
                end
            join
            done++;
            `WRITE_VERBOSE(("All forked processes ended at time %0t\n", $time));
        endtask
    endclass

    initial begin
        ForkClass fc = new;
        fc.do_fork;
        if (fc.done != 4 || $time != 70) $stop;
    end

    initial #101 $stop; // timeout
endmodule
