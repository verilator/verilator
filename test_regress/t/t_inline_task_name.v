// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
// SPDX-FileCopyrightText: 2026 Wilson Snyder

// verilog_format: off
`define stop $stop
`define check(got ,exp) do if ((got) !== (exp)) begin $write("%%Error: %s:%0d: $time=%0t got='h%x exp='h%x\n", `__FILE__,`__LINE__, $time, (got), (exp)); `stop; end while(0)
// verilog_format: on

module t;

  logic clk = 0;
  always #5 clk = ~clk;

  integer cyc = 0;

  int a_out;
  int b_out;
  int c_out;

  suba ua(.clk(clk), .base(32'd10), .out(a_out));
  suba ub(.clk(clk), .base(32'd20), .out(b_out));
  subb uc(.clk(clk), .base(32'd30), .out(c_out));

  function automatic int twiddle(int x);
    return x + 1;
  endfunction

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 3) begin
      `check(twiddle(0), 1);
      `check(a_out, 12);
      `check(b_out, 22);
      `check(c_out, 33);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module suba(input clk, input int base, output int out);
  /*verilator inline_module*/

  int val;

  function automatic int twiddle(int x);
    return x + 2;
  endfunction

  task automatic compute(input int x, output int y);
    y = twiddle(x);
  endtask

  always @(posedge clk) begin
    compute(base, val);
    out <= val;
  end
endmodule

module subb(input clk, input int base, output int out);
  /*verilator no_inline_module*/

  int val;

  function automatic int twiddle(int x);
    return x + 3;
  endfunction

  task automatic compute(input int x, output int y);
    y = twiddle(x);
  endtask

  always @(posedge clk) begin
    compute(base, val);
    out <= val;
  end
endmodule
