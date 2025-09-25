// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    int x = 0;
    begin : blk
      fork : fork_blk
        begin
          x = 1;
          #2;
          x = 2;
        end
      join_none
      #1;
    disable blk;
    end
    #2;
    if (x != 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
