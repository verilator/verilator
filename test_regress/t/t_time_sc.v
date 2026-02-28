// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  integer cyc = 0;

  time texpect = `TEST_EXPECT;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) begin
      $printtimescale;
      $write("[%0t] In %m: Hi - expect this is %0t\n", $time, texpect);
      if ($time != texpect) begin
        $write("[%0t] delta = %d\n", $time, $time - texpect);
        $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
    end

  end
endmodule
