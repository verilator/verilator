// DESCRIPTION: Verilator: DPI-hooks on arrays read through non-constant indices
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module regfile (
    input logic clk,
    input logic [2:0] wa,
    input logic [7:0] wd,
    input logic [2:0] ra1,
    input logic [1:0] ra2,
    output logic [7:0] rd1,
    output logic [7:0] rd2,
    output logic [7:0] rd5,
    output logic [7:0] rd6,
    output logic [7:0] rdw
);
  logic [7:0] rf[8];

  logic [7:0] wm[4];

  initial for (int i = 0; i < 8; i++) rf[i] = 8'h10 * 8'(i);
  initial for (int i = 0; i < 4; i++) wm[i] = 8'h0c * 8'(i);

  always @(posedge clk) rf[wa] <= wd;
  always @(posedge clk) wm[wa[1:0]] <= wd ^ 8'hff;

  assign rd1 = rf[ra1];
  /* verilator lint_off WIDTHEXPAND */
  assign rd2 = rf[ra2];
  /* verilator lint_on WIDTHEXPAND */
  assign rd5 = rf[5];
  assign rd6 = rf[6];
  assign rdw = wm[ra2];
endmodule

module top_module;
  logic clk = 0;
  int cyc = 0;
  logic [2:0] wa, ra1, rax;
  logic [1:0] ra2;
  logic [7:0] wd, rd1, rd2, rd5, rd6, rdw, o_xmr;

  assign wa = 3'(cyc + 2);
  assign wd = 8'ha0 + cyc[7:0];
  assign ra1 = 3'(cyc + 3);
  assign ra2 = cyc[1:0];
  assign rax = 3'(8 - cyc);

  regfile u (
      .clk(clk),
      .wa(wa),
      .wd(wd),
      .ra1(ra1),
      .ra2(ra2),
      .rd1(rd1),
      .rd2(rd2),
      .rd5(rd5),
      .rd6(rd6),
      .rdw(rdw)
  );

  assign o_xmr = u.rf[rax];

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    $display("[%0d] rd1[%0d]=%02x rd2[%0d]=%02x rd5=%02x rd6=%02x xmr[%0d]=%02x rdw=%02x", cyc, ra1,
             rd1, ra2, rd2, rd5, rd6, rax, o_xmr, rdw);
    if (cyc > 7) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
