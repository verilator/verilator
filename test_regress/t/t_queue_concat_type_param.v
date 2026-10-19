// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

// Concatenations to arrays of a type parameter, widthed for each specialization
module sub #(
    parameter type T = int
);
  // verilator lint_off WIDTHTRUNC
  T a[$] = {1, 300};
  // verilator lint_on WIDTHTRUNC
  T q[$] = {a, T'(300)};
  T d[] = {a, T'(300)};
endmodule

module t;
  sub #(.T(int)) u_int ();
  sub #(.T(byte)) u_byte ();

  initial begin
    `checkh(u_int.a[1], 300);
    `checkh(u_int.q[2], 300);
    `checkh(u_int.d[2], 300);
    `checkh(u_byte.a[1], 8'sd44);
    `checkh(u_byte.q[2], 8'sd44);
    `checkh(u_byte.d[2], 8'sd44);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
