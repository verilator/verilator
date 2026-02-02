// DESCRIPTION: Verilator: Test nested interface as port connection
// Issue #5066
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-License-Identifier: CC0-1.0

interface A;
    logic x;
endinterface

interface B;
    A a();
endinterface

module M(A a);
    initial begin
        a.x = 1'b1;
    end
endmodule

module t;
    B b();
    M m(b.a);

    initial begin
        #1;
        if (b.a.x !== 1'b1) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
