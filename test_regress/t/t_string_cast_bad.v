// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input wire i
);

  parameter string P = "A";

  wire [119:0] o;
  wire [31:0] po;
  string s;
  logic [31:0] v;
  real r;

  assign o = string'(i ? "a" : "b");
  assign po = P;

  sub u_sub(.x(s));

  function int f(input int x);
    return x;
  endfunction

  function int g;
    return s;
  endfunction

  initial begin
    s = "a";
    v = s;
    v = signed'(s);
    r = s;
    v = f(s);
    v = g();
    $stop;
  end

endmodule

module sub (
    input int x
);
endmodule
