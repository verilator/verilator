// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  reg [7:0] da0[*];
  reg [7:0] da1[2][*];

  integer cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      da0[1] = 8'h11;
      da1[0][2] = 8'h22;
      da1[1][3] = 8'h33;
    end else if (cyc == 1) begin
      `checkh(da0.size(), 1);
      `checkh(da0[1], 8'h11);
      `checkh(da1[0].size(), 1);
      `checkh(da1[0][2], 8'h22);
      `checkh(da1[1][3], 8'h33);

      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
