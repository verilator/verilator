// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off MULTIDRIVEN
module t (/*AUTOARG*/
  // Inputs
  clk
  );
  input clk;

  logic [31:0] lhs1, lhs2, rhs;
  logic cond = 0;

  always_comb lhs1 = rhs;
  assign lhs2 = rhs;

  always @(posedge clk) rhs = '1;

  always @(negedge clk) begin
    if (cond) begin
      force lhs1 = 'hdeadbeef;
      force lhs2 = 'hfeedface;
    end
    else begin
      release lhs1;
      release lhs2;
    end
  end

  int cyc = 0;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) cond <= 1;
    if (cyc == 3) cond <= 0;
    if (cyc > 1 && cyc < 4) begin
        if (lhs1 != 'hdeadbeef) $stop;
        if (lhs2 != 'hfeedface) $stop;
    end
    if (cyc > 4 && cyc < 8) begin
        if (lhs1 != '1) $stop;
        if (lhs2 != '1) $stop;
    end
    if (cyc >= 8) begin
        $write("*-* All Finished *-*\n");
        $finish;
    end
  end
endmodule
