// DESCRIPTION: Verilator: Distinct delay times resume in time order
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Spawned out of time order; two waiters share #2000 and must stay FIFO.

module t;
  int seen[0:7];
  int n;

  initial begin
    fork
      begin
        #5000;
        seen[n++] = 5;
      end
      begin
        #10;
        seen[n++] = 1;
      end
      begin
        #2000;
        seen[n++] = 3;
      end
      begin
        #3000;
        seen[n++] = 4;
      end
      begin
        #2000;
        seen[n++] = 6;
      end
      begin
        #20;
        seen[n++] = 2;
      end
    join
    if (n != 6) begin
      $display("%%Error: n=%0d exp=6", n);
      $stop;
    end
    if (seen[0] != 1 || seen[1] != 2 || seen[2] != 3 || seen[3] != 6 || seen[4] != 4
        || seen[5] != 5) begin
      $display("%%Error: order %0d %0d %0d %0d %0d %0d", seen[0], seen[1], seen[2], seen[3],
               seen[4], seen[5]);
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
