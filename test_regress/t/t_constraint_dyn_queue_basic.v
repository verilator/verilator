// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class ConstrainedDynamicQueueArray;
    rand int queue_1d[$];
    rand int queue[$][$];
    rand int dyn[][];
    rand int queue_dyn[$][];
    rand int dyn_queue[][$];
    rand int queue_unp[$][3];
    rand int unp_queue[3][$];

    // Constraints for the queues and dynamic arrays
    constraint queue_constraints {
        foreach (queue_1d[i]) queue_1d[i] == i + 2;
        foreach (queue[i, j]) queue[i][j] == (2 * i) + j;
    }

    constraint dyn_constraints {
        dyn[0][0] == 10;
        dyn[1][0] inside {20, 30, 40};
        dyn[1][1] > 50;
        dyn[0][1] < 100;
        dyn[0][2] inside {5, 15, 25};
    }

    constraint queue_dyn_constraints {
        foreach (queue_dyn[i, j]) queue_dyn[i][j] == i + j + 3;
    }

    constraint dyn_queue_constraints {
        foreach (dyn_queue[i, j]) dyn_queue[i][j] == (3 * i) + j + 2;
    }

    constraint unp_queue_constraints {
        foreach (unp_queue[i, j]) unp_queue[i][j] == (i * 5) + j + 1;
    }

    // Constructor
    function new();
        queue_1d = {1, 2, 3, 4};
        queue = '{ '{1, 2}, '{3, 4, 5}, '{6}};
        dyn = new[2];
        dyn[0] = new[3];
        dyn[1] = new[4];

        queue_dyn = {};
        queue_dyn[0] = new[3];
        queue_dyn[1] = new[4];

        dyn_queue = new[2];
        dyn_queue[0] = {7, 8, 9};
        dyn_queue[1] = {10};

        queue_unp = {};

        unp_queue[0] = {17, 18};
        unp_queue[1] = {19};
        unp_queue[2] = {20};
    endfunction

    // Self-check function
    function void check();
        foreach (queue_1d[i]) begin
            if (queue_1d[i] != i + 2) begin
                $display("Error: queue_1d[%0d] = %0d does not meet constraint", i, queue_1d[i]);
                $stop;
            end
        end

        foreach (queue[i, j]) begin
            if (queue[i][j] != (2 * i) + j) begin
                $display("Error: queue[%0d][%0d] = %0d does not meet constraint", i, j, queue[i][j]);
                $stop;
            end
        end

        if (dyn[0][0] != 10 || !(dyn[1][0] inside {20, 30, 40}) || dyn[1][1] <= 50 || dyn[0][1] >= 100 || !(dyn[0][2] inside {5, 15, 25})) begin
            $display("Error: dyn array constraints not met.");
            $stop;
        end

        foreach (queue_dyn[i, j]) begin
            if (queue_dyn[i][j] != i + j + 3) begin
                $display("Error: queue_dyn[%0d][%0d] = %0d does not meet constraint", i, j, queue_dyn[i][j]);
                $stop;
            end
        end

        foreach (dyn_queue[i, j]) begin
            if (dyn_queue[i][j] != (3 * i) + j + 2) begin
                $display("Error: dyn_queue[%0d][%0d] = %0d does not meet constraint", i, j, dyn_queue[i][j]);
                $stop;
            end
        end

        if (unp_queue[0][0] != (0 * 5) + 0 + 1) begin
            $display("Error: unp_queue[0][0] = %0d does not meet constraint", unp_queue[0][0]);
            $stop;
        end

        if (unp_queue[0][1] != (0 * 5) + 1 + 1) begin
            $display("Error: unp_queue[0][1] = %0d does not meet constraint", unp_queue[0][1]);
            $stop;
        end

        if (unp_queue[1][0] != (1 * 5) + 0 + 1) begin
            $display("Error: unp_queue[1][0] = %0d does not meet constraint", unp_queue[1][0]);
            $stop;
        end

        if (unp_queue[2][0] != (2 * 5) + 0 + 1) begin
            $display("Error: unp_queue[2][0] = %0d does not meet constraint", unp_queue[2][0]);
            $stop;
        end
    endfunction
endclass

module t_constraint_dyn_queue_basic;
    ConstrainedDynamicQueueArray array_test;
    int success;
    initial begin
        $display("Test: Randomization for dynamic and mixed queues and arrays:");
        array_test = new();
        repeat(2) begin
            success = array_test.randomize();
            if (success != 1) begin
                $display("Randomization failed.");
                $stop;
            end
            array_test.check();
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
