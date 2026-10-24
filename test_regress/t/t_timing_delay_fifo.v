// DESCRIPTION: Verilator: Equal-time delayed coroutine resume stays FIFO
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  int seen[0:31];
  int n;

  initial begin
    // Eight waiters at time 5. First resume also enqueues two more at time 5;
    // those must follow the original eight.
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
    if (n != 10) begin
      $display("%%Error: n=%0d exp=10", n);
      $stop;
    end
    for (int i = 0; i < 8; i++) begin
      if (seen[i] != i) begin
        $display("%%Error: seen[%0d]=%0d exp=%0d", i, seen[i], i);
        $stop;
      end
    end
    if (seen[8] != 100 || seen[9] != 101) begin
      $display("%%Error: late same-time got %0d %0d", seen[8], seen[9]);
      $stop;
    end

    // Drained bucket's vector is spare. Another same-time group, then a lone
    // waiter, must resume cleanly (recycle path).
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
    if (n != 18) begin
      $display("%%Error: after reuse n=%0d exp=18", n);
      $stop;
    end
    for (int i = 0; i < 8; i++) begin
      if (seen[10 + i] != 200 + i) begin
        $display("%%Error: reuse seen[%0d]=%0d exp=%0d", 10 + i, seen[10 + i], 200 + i);
        $stop;
      end
    end
    fork
      begin
        #1;
        seen[n++] = 300;
      end
    join_none
    #2;
    if (n != 19 || seen[18] != 300) begin
      $display("%%Error: lone after reuse n=%0d seen=%0d", n, seen[18]);
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
