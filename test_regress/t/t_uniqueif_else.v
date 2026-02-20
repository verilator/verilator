// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic clk;
  logic A, B, C;
  logic reset;
  logic x;

  always #1 clk = ~clk;

  initial begin
    clk = 0;
    reset = 0;
    A = 0;
    B = 0;
    C = 0;
    #10;
    reset = 1;
    #2;
    A = 1;
    #2;
    `checkd(x, 1'b0);

    #2;
    B = 1;
    #2;
    `checkd(x, 1'b0);

    #2;
    B = 0;
    C = 1;
    #2;
    `checkd(x, 1'b1);

    #10;
    $finish;
  end

  always_ff @(posedge clk or negedge reset) begin
    if (!reset) begin
      x <= '0;
    end
    else if (A) begin
      unique if (B) begin
        x <= '0;
      end
      else if (C) begin
        x <= '1;
      end
      // This passes:
      // else begin end
      else;  // For unique if to not have a false positive
    end
  end

endmodule
