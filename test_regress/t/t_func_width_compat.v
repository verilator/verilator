// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define WIDE_W    3000
`define WIDER_W   4000
`define WIDEST_W  5000

module t();
  task automatic do_something(bit [`WIDEST_W-1:0] widest);
    /*verilator no_inline_task*/
    if (widest != 14'h06)
      $stop;
  endtask

  task automatic do_something_else(bit [`WIDER_W-1:0] wider);
    /*verilator no_inline_task*/
    if (wider != `WIDER_W'h06)
      $stop;
  endtask

  initial begin
    bit [`WIDE_W-1:0] wide;
    bit [`WIDER_W-1:0] wider;
    bit [`WIDEST_W-1:0] widest;

    wide = `WIDE_W'h06;
    widest = wide;
    wider = widest;

    if (wider != `WIDEST_W'h06)
      $stop;

    do_something(wider); // Expand
    do_something_else(widest); // Truncate

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
