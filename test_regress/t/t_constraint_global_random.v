// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class Inner;
    rand int val;
    constraint c_local { val inside {[1:5]}; }
    function new(); val = 0; endfunction
endclass

class Mid;
    int limit;
    rand int x;
    rand Inner inner;
    constraint c_mid { x == limit; }
    function new(int lim);
        limit = lim;
        inner = new();
    endfunction
endclass

class Top;
    rand Mid m1;
    rand Mid m2;
    rand int y;

    constraint c_global {
        m1.inner.val < m2.inner.val;
        y > m1.x;
        y < m2.x;
        m1.inner.val + m2.inner.val < 8;
    }

    function new();
        m1 = new(3);
        m2 = new(5);
        y = 0;
    endfunction
endclass

module t_constraint_global_random;
    int success;
    Top t;

    initial begin
        t = new();

        // Test 1: Regular randomize() with global constraints
        success = t.randomize();
        if (success != 1) $stop;

        // $display("m1.x=%0d, m2.x=%0d, y=%0d", t.m1.x, t.m2.x, t.y);
        // $display("m1.inner.val=%0d, m2.inner.val=%0d", t.m1.inner.val, t.m2.inner.val);

        if (t.m1.x != 3 || t.m2.x != 5) $stop;
        if (t.m1.inner.val >= t.m2.inner.val) $stop;
        if (t.y <= t.m1.x || t.y >= t.m2.x) $stop;
        if (t.m1.inner.val + t.m2.inner.val >= 8) $stop;
        if (t.m1.inner.val < 1 || t.m1.inner.val > 5 ||
            t.m2.inner.val < 1 || t.m2.inner.val > 5) $stop;

        // Test 2: randomize() with inline constraint on global-constrained members
        success = 0;
        success = t.randomize() with {
            m1.inner.val == 2;
            m2.inner.val == 5;
        };
        if (success != 1) $stop;

        // Verify inline constraints
        if (t.m1.inner.val != 2) $stop;
        if (t.m2.inner.val != 5) $stop;

        // Verify global constraints still hold
        if (t.m1.x != 3 || t.m2.x != 5) $stop;
        if (t.m1.inner.val >= t.m2.inner.val) $stop;
        if (t.y <= t.m1.x || t.y >= t.m2.x) $stop;
        if (t.m1.inner.val + t.m2.inner.val >= 8) $stop;

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
