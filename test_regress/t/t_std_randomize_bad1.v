// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

module t_std_randomize_bad1;
    bit [3:0] a;

    function int run();
        int success;
        success = std::randomize(a + 1); // ERROR: argument is not a variable
        return success;
    endfunction

    initial begin
        int ok;
        ok = run();
        if (ok == 0) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
