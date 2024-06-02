// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

    function int unsigned nth_power_of_2(input int unsigned n);
        nth_power_of_2 = 1;
        while (n != 0) begin
            n = n - 1;
            nth_power_of_2 = nth_power_of_2 << 1;
        end
    endfunction

    initial begin
        // Evaluating the function call in the loop condition used
        // to cause an infinite loop at run-time
        while (nth_power_of_2(8) != 256) begin
            $display("2**8 != 256 ?!");
            $stop;
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule
