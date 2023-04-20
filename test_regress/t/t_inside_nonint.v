// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

task foo(string s, real d);
  if (s inside {"RW", "WO"})
    $display("string: %s", s);
  if (d inside {0.0, 2.5})
    $display("real: %f", d);
endtask : foo

module t();
  initial begin
    $display("CALL 1:");
    foo("WO", 0.0);
    $display("CALL 2:");
    foo("ABC", 1.0);
    $display("CALL 3:");
    foo("RW", 2.0);
    $display("CALL 4:");
    foo("ABC", 2.5);

    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
