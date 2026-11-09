// DESCRIPTION: Verilator: Distinct delay times resume in time order
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
// verilog_format: off
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// Spawned out of time order; two waiters share #2000 and must stay FIFO.
// Then one waiter per distinct time, spawned longest-first.

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
    `checkd(n, 6);
    `checkd(seen[0], 1);
    `checkd(seen[1], 2);
    `checkd(seen[2], 3);
    `checkd(seen[3], 6);
    `checkd(seen[4], 4);
    `checkd(seen[5], 5);

    n = 0;
    for (int i = 7; i >= 0; i--) begin
      automatic int k = i;
      fork
        begin
          case (k)
            0: #1;
            1: #2;
            2: #3;
            3: #5;
            4: #8;
            5: #13;
            6: #21;
            default: #34;
          endcase
          seen[n++] = k;
        end
      join_none
    end
    #64;
    `checkd(n, 8);
    for (int i = 0; i < 8; i++) `checkd(seen[i], i);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
