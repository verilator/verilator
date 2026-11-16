// DESCRIPTION: Verilator: Release kept ports when inlined and do not keep interface ports
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module lane (
    input logic [6:0] i,
    output logic [6:0] o
);
  /*verilator inline_module*/
  assign o = (i * 7'd3) ^ 7'h53;
endmodule

interface link (
    input logic [6:0] i,
    output logic [6:0] o
);
  logic [6:0] copy_i;
  assign copy_i = i;
  assign o = (copy_i * 7'd3) ^ 7'h53;
endinterface

module t;
  logic [6:0] a, b;
  wire [6:0] x, y, ix, iy;
  lane u0 (
      a,
      x
  );
  lane u1 (
      b,
      y
  );
  link i0 (
      a,
      ix
  );
  link i1 (
      b,
      iy
  );

  initial begin
    for (int k = 0; k < 32; ++k) begin
      a = 7'(3 * k + 1);
      b = 7'(7 * k + 9);
      #1;
      `checkh(x, (a * 7'd3) ^ 7'h53);
      `checkh(y, (b * 7'd3) ^ 7'h53);
      `checkh(ix, (a * 7'd3) ^ 7'h53);
      `checkh(iy, (b * 7'd3) ^ 7'h53);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
