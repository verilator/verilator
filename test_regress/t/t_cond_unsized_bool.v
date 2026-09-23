// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 David Harris
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  logic a, b;
  logic [1:0] q_cond;
  logic [1:0] q_if;

  // Unsized condition (b & 1) in a nested conditional and an if (#8465)
  assign q_cond = a ? 2'd0 : (b & 1) ? 2'd1 : 2'd0;

  always_comb begin
    if (a) q_if = 2'd0;
    else if (b & 1) q_if = 2'd1;
    else q_if = 2'd0;
  end

  initial begin
    for (int i = 0; i < 4; ++i) begin
      {a, b} = i[1:0];
      #1;
      `checkh(q_cond, {1'b0, ~a & b});
      `checkh(q_if, {1'b0, ~a & b});
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
