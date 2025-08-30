// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Cls;
  int x = 0;
  int y = 0;

  task disable_outside_fork;
    fork : fork_blk
      begin
        x = 1;
        #2;
        x = 2;
      end
    join_none
    #1;
    disable fork_blk;
  endtask

  task disable_inside_fork;
    fork : fork_blk
      begin
        y = 1;
        disable fork_blk;
        y = 2;
      end
    join_none
  endtask
endclass

module t (  /*AUTOARG*/);
  initial begin
    Cls c = new;
    c.disable_outside_fork();
    #2;
    if (c.x != 1) $stop;
    c.disable_inside_fork();
    if (c.y != 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
