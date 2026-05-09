// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t (
   input clk
);
  integer cyc = 0;
  logic [127:0] sig;

  always @(posedge clk) begin
    cyc  <= cyc + 1;
    sig  <= '0;

    if (cyc == 1) begin
      force sig[31] = 1'b1;
      force sig[32] = 1'b1;
    end
    else if (cyc == 3) begin
      // width <= 8
      `checkh(sig[33:26], 8'h60);

      // 8 < width <= 16
      `checkh(sig[39:24], 16'h180);

      // width <= 32
      `checkh(sig[40:20], 21'h1800);

      // 32 < width <= 64
      `checkh(sig[50:10], 41'h600000);

      // width > 64
      `checkh(sig[100:5], (96'h1 << 26) | (96'h1 << 27));

      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
