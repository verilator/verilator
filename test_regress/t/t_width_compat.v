// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t();
  task automatic do_something(bit [13:0] widest);
    $display("%d", widest);
    if (widest != 14'h06)
      $stop;
  endtask

  initial begin
    bit [7:0] wide;
    bit [9:0] wider;

    wide = 8'h6;
    wider = wide;

    $display("%d", wider);
    if (wider != 10'h06)
      $stop;

    do_something(wider);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
