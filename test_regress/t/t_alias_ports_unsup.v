// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  wire [31:0] a, b;

  integer cyc = 0;
  assign a = cyc;

  sub s (
      .a(a),
      .b(b)
  );

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (a != cyc) $stop;
    if (b != cyc) $stop;

    $write("*-* All Finished *-*\n");
    $finish;

  end
endmodule

module sub (
    inout wire [31:0] a,
    inout wire [31:0] b
);
  alias a = b;
endmodule
