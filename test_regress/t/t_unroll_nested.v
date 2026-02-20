// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`ifndef VERILATOR
 `define PRAGMA
`elsif TEST_DISABLE
 `define PRAGMA /*verilator unroll_disable*/
`elsif TEST_FULL
 `define PRAGMA /*verilator unroll_full*/
`endif

module t;

  int a, b;
  int pos;

  initial begin
    for (int exit_a = 0; exit_a < 2; ++exit_a) begin
      `PRAGMA
      for (int exit_b = 0; exit_b < 3; ++exit_b) begin
        `PRAGMA
        b = 0;
        $write("exit_a %0d %0d", exit_a, exit_b);
        for (a = 0; a < 3; ++a) begin : a_loop
          `PRAGMA
          $write("  A%0d", a * 10 + b);
          for (b = 0; b < 3; ++b) begin : b_loop
            `PRAGMA
            $write(" B%0d", a * 10 + b);
            if (exit_b == 1 && b == 1) disable b_loop;
            $write(" C%0d", a * 10 + b);
            if (exit_b == 2 && a == 1) disable a_loop;
            $write(" D%0d", a * 10 + b);
          end
          $write("  Y%0d", a * 10 + b);
          if (exit_a == 1 && a == 1) disable a_loop;
          $write("  Z%0d", a * 10 + b);
        end
        $display;
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
