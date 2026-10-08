// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  localparam logic [3:0] a = 4'hDF;
  localparam logic [3:0] b = 4'b10101111;
  localparam logic [7:0] c = 8'd1234567890;

  initial begin
    // IEEE 1800-2023 "5.7.1 Integer literal constants":
    // If the size of the unsigned number is larger than the size
    // specified for the literal constant, the unsigned number shall
    // be truncated from the left.
    `checkd(a, 4'hF)
    `checkd(b, 4'b1111)
    `checkd(c, 8'hd2)
    $finish;
  end
endmodule
