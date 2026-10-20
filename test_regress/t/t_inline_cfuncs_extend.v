// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  reg [3:0] a;
  reg [3:0] b;
  reg lt_00, lt_01, lt_10, lt_11;

  always @(*) begin : blk
    reg [3:0] a_l;
    reg [3:0] b_l;
    a_l = a;
    b_l = b;
    lt_00 = $signed({1'b0, a_l}) < $signed({1'b0, b_l});
    lt_01 = $signed({1'b0, a_l}) < $signed({1'b1, b_l});
    lt_10 = $signed({1'b1, a_l}) < $signed({1'b0, b_l});
    lt_11 = $signed({1'b1, a_l}) < $signed({1'b1, b_l});
  end

  initial begin
    a = 4'd15;
    b = 4'd3;
  end

  always @(posedge clk) begin
    `checkd(lt_00, 1'b0);
    `checkd(lt_01, 1'b0);
    `checkd(lt_10, 1'b1);
    `checkd(lt_11, 1'b0);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
