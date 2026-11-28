// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module sub (
    input [6:0] a,
    output [6:0] o
);
  assign o = a + 7'd1;
endmodule

module t (
    input clk
);

  int cyc = 0;
  logic [6:0] x = 7'd3;
  logic en = 1'b0;
  wire [6:0] o;
  tri [6:0] bus;
  logic [6:0] last;  // Argument of the last 'logged_dbl' call
  logic [6:0] exp_last;

  function automatic [6:0] dbl(input [6:0] v);
    return v * 7'd2;
  endfunction

  function automatic [6:0] logged_dbl(input [6:0] v);
    last = v;
    return v * 7'd2;
  endfunction

  sub u (
      .a(x > 7'd1 && logged_dbl(x) != 7'd0 ? logged_dbl(x + 7'd1) : 7'h5),
      .o(o)
  );

  assign bus = en ? dbl(x) : 'z;
  assign bus = !en ? 7'h11 : 'z;

  always @(posedge clk) begin
    `checkh(o, (x > 7'd1 && 7'(x * 2) != 7'd0 ? 7'((x + 1) * 2) : 7'h5) + 7'd1);
    // 'x <= 1' skips both calls, 'x == 64' only the second
    if (x == 7'd64) exp_last = x;
    else if (x > 7'd1) exp_last = x + 7'd1;
    `checkh(last, exp_last);
    `checkh(bus, en ? 7'(x * 2) : 7'h11);
    cyc <= cyc + 1;
    x <= x + 7'd29;
    en <= ~en;
    if (cyc == 40) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
