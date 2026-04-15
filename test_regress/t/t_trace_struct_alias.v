// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;
  int cyc;

  typedef struct packed {
    logic [7:0] a;
    logic [7:0] b;
  } strp_t;

  strp_t s1;
  strp_t s2;

  strp_t s3;
  logic [7:0] alias_of_s3a;
  assign alias_of_s3a = s3.a;

  strp_t s4;
  strp_t s5;
  assign s5 = s4;

  logic [7:0] source_val;
  strp_t s6;
  assign s6.a = source_val;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    s1 <= {8'(cyc), 8'(cyc + 1)};
    s2 <= {8'(cyc + 2), 8'(cyc + 3)};
    s3 <= {8'(cyc + 4), 8'(cyc + 5)};
    s4 <= {8'(cyc + 6), 8'(cyc + 7)};
    source_val <= 8'(cyc + 8);
    s6.b <= 8'(cyc + 9);
    if (cyc == 9) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
