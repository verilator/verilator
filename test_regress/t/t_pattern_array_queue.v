// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t();
  byte array1[];
  byte array2[];
  byte queue1[$];
  byte queue2[$];
  byte byte_e;
  initial begin
    queue2 = {8'ha, 8'hb};
    array2 = {8'hc, 8'hd};
    byte_e = 8'he;

    array1 = {byte_e};
    `checkd(array1[0], 8'he);

    array1 = {queue2};
    `checkd(array1[0], 8'ha);
    `checkd(array1[1], 8'hb);

    array1 = {array2};
    `checkd(array1[0], 8'hc);
    `checkd(array1[1], 8'hd);

    queue1 = {byte_e};
    `checkd(queue1[0], 8'he);

    queue1 = {queue2};
    `checkd(queue1[0], 8'ha);
    `checkd(queue1[1], 8'hb);

    queue1 = {array2};
    `checkd(queue1[0], 8'hc);
    `checkd(queue1[1], 8'hd);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
