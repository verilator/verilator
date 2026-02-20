// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  integer cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) begin
      $write("[%0t] In %m: Hi\n", $time);
      $printtimescale;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
