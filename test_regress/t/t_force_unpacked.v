// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  integer cyc = 0;

  logic logic_arr[2][-2:2][-3:-5];
  int int_arr[-1:2][1][3];

  // Test loop
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      logic_arr[0][2][-4] <= 1;
      int_arr[0][0][2] <= 1;
    end
    else if (cyc == 1) begin
      `checkh(logic_arr[0][2][-4], 1);
      `checkh(int_arr[0][0][2], 1);
    end
    else if (cyc == 2) begin
      force logic_arr[0][2][-4] = 0;
      force int_arr[0][0][2] = 0;
    end
    else if (cyc == 3) begin
      `checkh(logic_arr[0][2][-4], 0);
      logic_arr[0][2][-4] <= 1;
      `checkh(int_arr[0][0][2], 0);
      int_arr[0][0][2] <= 1;
    end
    else if (cyc == 4) begin
      `checkh(logic_arr[0][2][-4], 0);
      `checkh(int_arr[0][0][2], 0);
    end
    else if (cyc == 5) begin
      release logic_arr[0][2][-4];
      release int_arr[0][0][2];
    end
    else if (cyc == 6) begin
      `checkh(logic_arr[0][2][-4], 0);
      logic_arr[0][2][-4] <= 1;
      `checkh(int_arr[0][0][2], 0);
      int_arr[0][0][2] <= 1;
    end
    else if (cyc == 7) begin
      `checkh(logic_arr[0][2][-4], 1);
      `checkh(int_arr[0][0][2], 1);
    end
    else if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
