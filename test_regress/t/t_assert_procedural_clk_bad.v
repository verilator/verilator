// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  integer cyc;
  initial cyc = 1;
  wire [7:0] cyc_copy = cyc[7:0];

  // Checking logic outside the procedure cannot read its automatic variables
  always @(negedge clk) begin
    for (int i = 0; i < 2; ++i) assert property (cyc[i] |=> cyc[i]);
  end

  // A reach cannot tell which event woke the procedure
  always @(negedge clk or cyc_copy) assert property (cyc[0] |=> cyc[1]);

  // A ranged cycle delay entered in the first cycle
  always @(negedge clk) if (cyc[0]) assert property (cyc[1] ##[0:2] cyc[2]);

  // A sequence 'and' with an operand ending in the first cycle
  always @(negedge clk) if (cyc[0]) assert property (cyc[1] and (cyc[2] ##1 cyc[3]));

  always @(posedge clk) begin
    if (cyc != 0) begin
      cyc <= cyc + 1;
      if (cyc == 9) begin
        assume property (@(posedge clk) cyc == 9);
        assume property (@(negedge clk) cyc == 9);
      end
      if (cyc == 10) begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    end
  end

endmodule
