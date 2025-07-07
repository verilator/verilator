// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

module t_std_randomize_bad1;
    bit [3:0] a;

    function bit run();
        bit success;
        success = std::randomize(a + 1); // ERROR: argument is not a variable
        // $display("a=%0h", a);
        return success;
    endfunction

    initial begin
        bit ok;
        ok = run();
        // $display("ok=%0d", ok);
        if (!ok) $stop;
    end
endmodule
