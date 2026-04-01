// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  logic clk = 0;
  always #5 clk = ~clk;

  initial begin
    #300;
    $write("*-* All Finished *-*\n");
    $finish;
  end

  localparam int N = 8;

  logic [N-1:0][7:0] i = '0;
  logic [N-1:0][7:0] o;

  always @(posedge clk) begin
    for (int n = 0; n < N; ++n) begin
      i[n] <= i[n] + 8'(n);
    end
  end

  for (genvar n = 0; n < N; ++n) begin
    assign o[n] = ~i[n];
  end

  always @(posedge clk) begin
    $write("%05t i == '{", $time);
    for (int n = 0; n < N; ++n) begin
      if (n > 0) $write(", ");
      $write("%2d: %4d", n, o[n]);
    end
    $write("}\n");
  end

endmodule
