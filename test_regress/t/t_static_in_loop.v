// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    static int x = 0;
    while (x < 10) begin : outer_loop
      static int y = 0;
      while (y < x) begin : inner_loop
        static int a = 0;
        a++;
        y++;
      end
      x++;
    end
    if (outer_loop.inner_loop.a != 9) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
