// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  // The untyped parameter is 32 bits wide for 5, but 8 bits for 8'd5, so they need different
  // libraries, but libraries are distinguished by parameter values only
  int width0, width1, width2;
  mid #(.P(5)) m0 (.width(width0));
  mid #(.P(8'd5)) m1 (.width(width1));
  // Likewise relative to the default value
  mid #(.P(8'd0)) m2 (.width(width2));
  always @(posedge clk) begin
    `checkd(width0, 32);
    `checkd(width1, 8);
    `checkd(width2, 8);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module mid #(
    parameter P = 0
) (
    output int width
);
  /*verilator hier_block*/
  assign width = $bits(P);
endmodule
