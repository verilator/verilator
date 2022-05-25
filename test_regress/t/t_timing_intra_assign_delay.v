// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
  int val1, val2;

  always @val1 $write("[%0t] val1=%0d val2=%0d\n", $time, val1, val2);

  assign #10 val2 = val1;

  initial begin
    val1 = 1;
    #10 val1 = 2;
    fork #5 val1 = 3; join_none
    val1 = #10 val1 + 2;
    val1 <= #10 val1 + 2;
    fork #5 val1 = 5; join_none
    #20 $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
