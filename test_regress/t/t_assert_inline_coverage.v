// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  integer cyc = 0;
  logic rst_n = 0;
  logic en = 0;
  logic q = 0;
  logic [7:0] cnt = 0;

  // Synchronous active-low reset driving runtime-varying signals, so the
  // asserted and covered properties are not constant-folded away.
  always_ff @(posedge clk) begin
    rst_n <= (cyc >= 2);
    en <= cyc[0];
    if (!rst_n) begin
      q <= 1'b0;
      cnt <= '0;
    end
    else if (en) begin
      q <= ~q;
      cnt <= cnt + 8'd1;
    end
  end

  a :
  assert property (@(posedge clk) !rst_n |=> q == 1'b0);

  c :
  cover property (@(posedge clk) disable iff (!rst_n) en && cnt == $past(cnt));

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
