// DESCRIPTION: Verilator: Split a block before making tables of it, avoiding a false loop
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic [1:0] n_r;
  logic v_i, clk;
  logic v_o, full_o, e0, e1, yumi_i;
  // 'v_o' and 'full_o' depend on 'n_r' and 'v_i' only, 'e0' and 'e1' also on 'yumi_i'.
  // A single table of all four, indexed by all inputs, would make 'v_o' depend on 'yumi_i'.
  always_comb begin
    case (n_r)
      2'b00: begin v_o = v_i; full_o = 1'b0; e0 = 1'b0; e1 = v_i & ~yumi_i; end
      2'b01: begin v_o = 1'b1; full_o = 1'b0; e0 = v_i & ~yumi_i; e1 = v_i & yumi_i; end
      2'b10: begin v_o = 1'b1; full_o = 1'b1; e0 = v_i & yumi_i; e1 = yumi_i; end
      default: begin v_o = 1'b0; full_o = 1'b0; e0 = 1'b0; e1 = 1'b0; end
    endcase
  end
  // The consumer takes what is valid
  assign yumi_i = v_o & clk;

  initial begin
    logic exp_v, exp_yumi;
    for (int i = 0; i < 16; ++i) begin
      n_r = 2'(i >> 2);
      v_i = 1'(i >> 1);
      clk = 1'(i);
      #1;
      exp_v = n_r == 2'b00 ? v_i : n_r != 2'b11;
      exp_yumi = exp_v & clk;
      `checkh(v_o, exp_v);
      `checkh(full_o, n_r == 2'b10);
      `checkh(yumi_i, exp_yumi);
      `checkh(e0, n_r == 2'b01 ? v_i & ~exp_yumi : n_r == 2'b10 ? v_i & exp_yumi : 1'b0);
      `checkh(e1, n_r == 2'b00 ? v_i & ~exp_yumi : n_r == 2'b01 ? v_i & exp_yumi
                  : n_r == 2'b10 ? exp_yumi : 1'b0);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
