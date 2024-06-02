// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
    class Sleeper;
        task sleep;
            event e;
            fork
                @e;
                #1 ->e;
            join;
        endtask
    endclass

    initial begin
        Sleeper sleeper = new;
        sleeper.sleep;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
