// DESCRIPTION: Verilator: Coalescing does not redirect references across scopes
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module lane(output logic [6:0] result);
  /*verilator no_inline_module*/
  wire [6:0] value;
  assign result = ((value * 7'd3) ^ 7'h55) + (value >> 2);
endmodule

module t;
  logic [6:0] a;
  logic [6:0] b;
  wire [6:0] x;
  wire [6:0] y;
  lane u0(x);
  lane u1(y);
  assign u0.value = a;
  assign u1.value = b;

  initial begin
    for (int i = 0; i < 32; ++i) begin
      a = 7'(3 * i + 1);
      b = 7'(7 * i + 9);
      #1;
      `checkh(x, 7'(((a * 7'd3) ^ 7'h55) + (a >> 2)));
      `checkh(y, 7'(((b * 7'd3) ^ 7'h55) + (b >> 2)));
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
