// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off WIDTHTRUNC */
class Inner;
    rand int x;
    rand int y;
endclass

class Middle;
    rand Inner obj;
    rand Inner arr[3];
endclass

class Outer;
    rand Middle mid;
    rand Middle mid_arr[2];

    function new();
        mid = new;
        mid.obj = new;
        foreach (mid.arr[i]) mid.arr[i] = new;
        foreach (mid_arr[i]) begin
            mid_arr[i] = new;
            mid_arr[i].obj = new;
            foreach (mid_arr[i].arr[j]) mid_arr[i].arr[j] = new;
        end
    endfunction

    // Case 1: Simple nested member access (should work)
    constraint c_simple {
        mid.obj.x == 100;
        mid.obj.y == 101;
    }

    // Case 2: Array indexing in the path (may not work)
    constraint c_array_index {
        mid.arr[0].x == 200;
        mid.arr[0].y == 201;
    }

    // Case 3: Nested array indexing
    constraint c_nested_array {
        mid_arr[0].obj.x == 300;
        mid_arr[0].obj.y == 301;
    }

    // Case 4: Multiple array indices
    constraint c_multi_array {
        mid_arr[1].arr[2].y == 400;
    }
endclass

module t_constraint_global_arr_unsup;
    initial begin
        Outer o = new;
        if (o.randomize()) begin
            $display("Case 1 - Simple: mid.obj.x = %0d (expected 100)", o.mid.obj.x);
            $display("Case 1 - Simple: mid.obj.y = %0d (expected 101)", o.mid.obj.y);
            $display("Case 2 - Array[0]: mid.arr[0].x = %0d (expected 200)", o.mid.arr[0].x);
            $display("Case 2 - Array[0]: mid.arr[0].y = %0d (expected 201)", o.mid.arr[0].y);
            $display("Case 3 - Nested[0]: mid_arr[0].obj.x = %0d (expected 300)", o.mid_arr[0].obj.x);
            $display("Case 3 - Nested[0]: mid_arr[0].obj.y = %0d (expected 301)", o.mid_arr[0].obj.y);
            $display("Case 4 - Multi[1][2]: mid_arr[1].arr[2].y = %0d (expected 400)", o.mid_arr[1].arr[2].y);

            // Check results
            if (o.mid.obj.x == 100 && o.mid.obj.y == 101 &&
                o.mid.arr[0].x == 200 && o.mid.arr[0].y == 201 &&
                o.mid_arr[0].obj.x == 300 && o.mid_arr[0].obj.y == 301 &&
                o.mid_arr[1].arr[2].y == 400) begin
                $display("*-* All Finished *-*");
                $finish;
            end else begin
                $display("*-* FAILED *-*");
                $stop;
            end
        end else begin
            $display("*-* FAILED: randomize() returned 0 *-*");
            $stop;
        end
    end
endmodule
/* verilator lint_off WIDTHTRUNC */
