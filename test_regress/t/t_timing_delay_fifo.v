// DESCRIPTION: Verilator: Equal-time delayed coroutine resume stays FIFO
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
// verilog_format: off
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  int seen[0:31];
  int n;

  initial begin
    // Eight waiters at time 5. First resume also enqueues two more at time 5;
    // those must follow the original eight (not append into the bucket being drained).
    for (int i = 0; i < 8; i++) begin
      automatic int k = i;
      fork
        begin
          #5;
          seen[n++] = k;
          if (k == 0) begin
            fork
              begin
                seen[n++] = 100;
              end
            join_none
            fork
              begin
                seen[n++] = 101;
              end
            join_none
          end
        end
      join_none
    end
    #10;
    `checkd(n, 10);
    for (int i = 0; i < 8; i++) `checkd(seen[i], i);
    `checkd(seen[8], 100);
    `checkd(seen[9], 101);

    // Another same-time group, then a lone waiter.
    for (int i = 0; i < 8; i++) begin
      automatic int k = i;
      fork
        begin
          #1;
          seen[n++] = 200 + k;
        end
      join_none
    end
    #2;
    `checkd(n, 18);
    for (int i = 0; i < 8; i++) `checkd(seen[10 + i], 200 + i);
    fork
      begin
        #1;
        seen[n++] = 300;
      end
    join_none
    #2;
    `checkd(n, 19);
    `checkd(seen[18], 300);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
