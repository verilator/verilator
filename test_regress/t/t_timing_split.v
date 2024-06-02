// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Jomit626.
// SPDX-License-Identifier: CC0-1.0

module t ();
    logic clk = 0;
    logic data = 0;

    always #5 clk <= ~clk;

    task static foo();
        @(negedge clk);
        data = 1;
        @(negedge clk);
        data = 0;
    endtask

`define foo8()\
  foo();foo();foo();foo();foo();foo();foo();foo()

`define foo64()\
  `foo8();`foo8();`foo8();`foo8();`foo8();`foo8();`foo8();`foo8()

`define foo512()\
  `foo64();`foo64();`foo64();`foo64();`foo64();`foo64();`foo64();`foo64()

    initial begin
        `foo512();
        `foo512();
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
