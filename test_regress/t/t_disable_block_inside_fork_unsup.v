// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    int x = 0, y = 0;
    fork : fork_blk
      begin : blk1
        y = 1;
        begin : blk2
          x = 1;
          disable blk2;
          #2;
          x = 2;
        end
      end
    join_none
    #3;
    if (x != 1) $stop;
    if (y != 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
