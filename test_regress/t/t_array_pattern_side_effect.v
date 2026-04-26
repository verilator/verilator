// DESCRIPTION: Verilator: Assignment pattern preserves array expression side effects
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-FileCopyrightText: 2026 Rowan Goemans
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  // verilator lint_off ASCRANGE
  typedef logic [0:2][7:0] triple_lv_t;
  // verilator lint_on ASCRANGE
  typedef triple_lv_t pair_t [0:1];

  function automatic triple_lv_t mk3(
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c
  );
    mk3 = '{0: a, 1: b, 2: c};
  endfunction

  pair_t pair;

  initial begin
    // verilator lint_off SIDEEFFECT
    pair = '{
      0: mk3(8'd1, 8'd2, 8'd3),
      1: mk3(8'd4, 8'd5, 8'd6)
    };
    // verilator lint_on SIDEEFFECT

    `checkd(pair[0][0], 8'd1);
    `checkd(pair[0][1], 8'd2);
    `checkd(pair[0][2], 8'd3);
    `checkd(pair[1][0], 8'd4);
    `checkd(pair[1][1], 8'd5);
    `checkd(pair[1][2], 8'd6);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
