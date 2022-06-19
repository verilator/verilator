// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
  int val;
  event e;

  always @val $write("val=%0d\n", val);

  initial begin
    val = 1;
    @e val = 2;
    fork begin
        @e #1 val = 3;
        ->e;
    end join_none
    ->e;
    val = @e val + 2;
    val <= @e val + 2;
    fork begin
        @e val = 5;
        ->e;
    end join_none
    ->e;
    ->e;
    #1 $write("*-* All Finished *-*\n");
    $finish;
  end

  initial #1 ->e;
endmodule
