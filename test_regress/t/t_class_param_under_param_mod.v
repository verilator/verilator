// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

/// Test for bug4301
// TODO: merge into t_class_dead

class foo #(int A = 0);
    function bit check(int val);
        return A == val;
    endfunction
endclass

module sub #(parameter int A = 0);
    foo #(A) obj;
endmodule

module t;
    sub #(100) i_sub();
    initial begin
        i_sub.obj = new;
        if (!i_sub.obj.check(100)) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule
