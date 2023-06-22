// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Jomit626.
// SPDX-License-Identifier: CC0-1.0

module t ();
    logic clk = 0;
    logic data = 0;

    always #5 clk <= ~clk;

    initial begin
        for(int i=0;i<4096;i++) begin
            @(negedge clk);
            data = 1;
            @(negedge clk);
            data = 0;
        end
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
