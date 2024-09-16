// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
    class Foo;
        task sleep;
            event e;
            fork
                @e;
                #1 ->e;
            join
        endtask
        task trigger_later1(event e);
            fork #2 ->e; join_none
        endtask
        task trigger_later2(ref event e);
            fork #3 ->e; join_none
        endtask
        task test;
            for (int i = 0; i < 10; i++) begin
                event e1, e2;
                trigger_later1(e1);
                trigger_later2(e2);
                sleep;
                @e1; @e2;
            end
        endtask
    endclass

    initial begin
        Foo foo = new;
        foo.test;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
