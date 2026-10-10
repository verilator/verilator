// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2009 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  reg signed [2:0] negcnt;
  integer times;
  initial begin
    times = 0;
    repeat (1) begin
      repeat (0) $stop;
      repeat (-1) $stop;
      negcnt = 'sb111;
      // Not all commercial simulators agree on the below stopping or not
      // verilator lint_off WIDTH
      repeat (negcnt) $stop;
      // verilator lint_on  WIDTH
      repeat (5) begin : repeat_5
        repeat (2) begin : repeat_2
          static integer static_var = 0;
          static_var = static_var + 1;
          times = times + 1;
        end
      end
      repeat (1) begin : repeat_1
        $info();
        repeat (1) begin : repeat_1_1
          $info();
        end
      end
    end
    if (times != 10) $stop;
    if (repeat_5.repeat_2.static_var != 10) $stop;
    //
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
