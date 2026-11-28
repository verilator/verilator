// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Eduardo Schwarz Danni
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  int cyc = 0;
  logic [62:0] crc = 63'h5aef0c8dd70a4497;
  logic [6:0] sum = 0;
  logic [32:0] acc = 0;
  logic [14:0] delayed;
  logic [14:0] seen = 0;

  assign #3 delayed = crc[14:0];

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[61:0], crc[62] ^ crc[61]};
    sum <= sum + crc[6:0];
    acc <= acc + {crc[31:0], crc[32]};
    seen <= seen ^ delayed;
    if (cyc == 99) begin
      $display("cyc=%0d sum=%0d acc=%0d seen=%0d time=%0t", cyc, sum, acc, seen, $time);
      `checkd(sum, 7'd5);
      `checkd(acc, 33'd2797282622);
      `checkd(seen, 15'd3773);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
