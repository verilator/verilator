// DESCRIPTION: Verilator: One waiter per distinct delay time
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Each delay is a different time (inline-only buckets). Spawn longest first;
// resume order must follow time.

module t;
  int wake[0:7];
  int n;

  initial begin
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
          wake[n++] = k;
        end
      join_none
    end
    #64;
    if (n != 8) begin
      $display("%%Error: n=%0d exp=8", n);
      $stop;
    end
    for (int i = 0; i < 8; i++) begin
      if (wake[i] != i) begin
        $display("%%Error: wake[%0d]=%0d exp=%0d", i, wake[i], i);
        $stop;
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
