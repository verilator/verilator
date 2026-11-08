// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Graeme Smecher
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off IEEEMAYDEPRECATE */
module t;
  logic [3:0] a[2];
  logic [3:0] q[$];
  logic [3:0] d[];
  wire [3:0] a2[2][2];
  logic [7:0] p;
  logic [3:0] f[2] /*verilator forceable*/;

  initial begin
    force a = q;
    force a = {>>{p}};
    assign a = q;
    assign a = {>>{p}};
    force a = d;
    force a2[0] = q;
    assign f = a;
  end
endmodule
