// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class bar;
    task foo(logic r);
        int a, b;
        if (r) return;
        fork a = #1 b; join_none
    endtask
endclass

module t;
    bar b = new;

    initial begin
        b.foo(0);
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
