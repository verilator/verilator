// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  bit p = 0, q = 0;

  initial begin
    t1(p);
    t2(q);
    if (p != 1) $stop;
    if (q != 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end

  task t1(inout p);
    fork
      p = 1;
    join_none
    #0;
  endtask

  task t2(output q);
    q = 1;
  endtask
endmodule
