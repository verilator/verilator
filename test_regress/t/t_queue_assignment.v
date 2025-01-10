// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

module t_queue_assignment;
    typedef int T_QI[$];
    T_QI jagged_array[$];   // int jagged_array[$][$];
    initial begin
        jagged_array = '{ {1}, T_QI'{2,3,4}, {5,6} };
        // jagged_array[0][0] = 1 -- jagged_array[0] is a queue of 1 int
        // jagged_array[1][0] = 2 -- jagged_array[1] is a queue of 3 ints
        // jagged_array[1][1] = 3
        // jagged_array[1][2] = 4
        // jagged_array[2][0] = 5 -- jagged_array[2] is a queue of 2 ints
        // jagged_array[2][1] = 6
        jagged_array.push_back('{7});
        jagged_array.push_back('{8, 9, 10});
        jagged_array.push_front('{0, 1});
        print_and_check();

        $write("*-* All Finished *-*\n");
        $finish;
    end

    task automatic print_and_check();
        integer i, j;
        int expected_values[][] = '{ '{0, 1}, '{1}, '{2, 3, 4}, '{5, 6}, '{7}, '{8, 9, 10} };

        for (i = 0; i < jagged_array.size(); i++) begin
            for (j = 0; j < jagged_array[i].size(); j++) begin
                // $display("jagged_array[%0d][%0d] = %0d", i, j, jagged_array[i][j]);
                if (jagged_array[i][j] !== expected_values[i][j]) begin
                    $stop;
                end
            end
        end
    endtask

endmodule
