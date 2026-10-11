// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A parameterized class reference inside the index of another (#8618)

class C #(
    int A = 0
);
  static bit [7:0] a[int];
  static int b[int];
  static bit [7:0] m[int][int];
  static bit [15:0] v;
  static function int f(int x);
    return x + A;
  endfunction
endclass

class D #(
    int A = 0
);
  static bit [7:0] a[int];
endclass

module t;
  bit [7:0] x;
  initial begin
    C#(0)::b[0] = 3;
    C#(0)::b[1] = 4;
    C#(0)::a[C#(0)::b[0]] = 1;  // Index of the same class
    `checkd(C#(0)::a[3], 1);
    D#(0)::a[C#(0)::b[0]] = 2;  // Index of another class
    `checkd(D#(0)::a[3], 2);
    x = C#(0)::a[C#(0)::b[0]];  // As a value
    `checkd(x, 1);
    C#(0)::m[C#(0)::b[0]][C#(0)::b[1]] = 5;  // Two indices
    `checkd(C#(0)::m[3][4], 5);
    C#(0)::v = 16'h1234;
    `checkd(C#(0)::v[C#(0)::b[1]+:4], 4'h3);  // Indexed part select
    `checkd(C#(0)::a[C#(5)::f(C#(0)::b[0]) - 5], 1);  // Call argument within an index
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
