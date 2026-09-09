// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Targets in generate loops (read directly (lane), read in expressions (lanx), in a nested loop
// (outer/inner), driven by a continuous assignment (lana))
module top_module;
  logic clk = 0;
  int   cyc = 0;
  logic [7:0] r = 0;
  logic [7:0] o_alone, o_pair, o_right;
  logic [7:0] iv = 8'h10;
  logic [7:0] viaAssign;

  genvar i, j;
  generate
    for (i = 0; i < 2; i++) begin : lane
      logic [7:0] cnt;
      always @(posedge clk) cnt <= cyc[7:0] + i;
    end
    for (i = 0; i < 2; i++) begin : lanx
      logic [7:0] cnt;
      always @(posedge clk) cnt <= cyc[7:0] + i;
    end
    for (i = 0; i < 2; i++) begin : outer
      for (j = 0; j < 2; j++) begin : inner
        logic [7:0] cnt;
        always @(posedge clk) cnt <= cyc[7:0] + (i * 8'd16) + j;
      end
    end
    for (genvar g = 0; g < 2; g++) begin : lana
      logic [7:0] cnt;
      assign cnt = iv + g[7:0];
    end
  endgenerate

  assign o_alone = lanx[0].cnt;
  assign o_pair = lanx[0].cnt ^ lanx[1].cnt;
  assign o_right = r ^ lanx[0].cnt;
  assign viaAssign = lana[1].cnt;

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    r <= 8'h3c ^ cyc[7:0];
    $display("$[%0d| l0: %02x l1: %02x]", cyc, lane[0].cnt, lane[1].cnt);
    $display("[%0d] alone=%02x pair=%02x right=%02x", cyc, o_alone, o_pair, o_right);
    $display("$[%0d| 00:%02x 01:%02x 10:%02x 11:%02x]", cyc,
             outer[0].inner[0].cnt, outer[0].inner[1].cnt,
             outer[1].inner[0].cnt, outer[1].inner[1].cnt);
    $display("[%0d] direct=%02x viaAssign=%02x", cyc, lana[1].cnt, viaAssign);
    if (cyc > 6) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
