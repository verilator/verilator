// DESCRIPTION: Verilator: Hierarchical coverage merge with three generated datasets
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module work_unit (
    input logic clk,
    input logic rst,
    input logic sel,
    input logic [2:0] value
);
  logic [2:0] acc;

  always_ff @(posedge clk) begin
    if (rst) begin
      acc <= 3'b0;
    end else if (sel) begin
      acc <= acc + value;
    end else begin
      acc <= acc ^ value;
    end
  end
endmodule

module mid_wrapper (
    input logic clk,
    input logic rst,
    input logic sel,
    input logic [2:0] value
);
  work_unit u_work (
      .clk(clk),
      .rst(rst),
      .sel(sel),
      .value(value)
  );
endmodule

module other_unit (
    input logic clk,
    input logic rst,
    input logic enable,
    input logic [2:0] value
);
  logic [2:0] acc;

  always_ff @(posedge clk) begin
    if (rst) begin
      acc <= 3'b0;
    end else if (enable && value[0]) begin
      acc <= acc + 3'd1;
    end else begin
      acc <= acc + 3'd2;
    end
  end
endmodule

module tb_same_a;
  logic clk = 0;
  logic rst = 1;
  logic sel = 0;
  logic [2:0] value = 3'd1;
  int cyc = 0;

  always #1 clk = !clk;

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    rst <= (cyc == 0);
    sel <= cyc[0];
    value <= value + 3'd1;
    if (cyc == 6) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  work_unit u_work (
      .clk(clk),
      .rst(rst),
      .sel(sel),
      .value(value)
  );
endmodule

module tb_same_b;
  logic clk = 0;
  logic rst = 1;
  logic sel = 1;
  logic [2:0] value = 3'd3;
  int cyc = 0;

  always #1 clk = !clk;

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    rst <= (cyc == 0);
    sel <= !sel;
    value <= value + 3'd2;
    if (cyc == 6) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  mid_wrapper u_mid (
      .clk(clk),
      .rst(rst),
      .sel(sel),
      .value(value)
  );
endmodule

module tb_other;
  logic clk = 0;
  logic rst = 1;
  logic enable = 0;
  logic [2:0] value = 3'd5;
  int cyc = 0;

  always #1 clk = !clk;

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    rst <= (cyc == 0);
    enable <= (cyc != 2);
    value <= value + 3'd1;
    if (cyc == 6) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  other_unit u_other (
      .clk(clk),
      .rst(rst),
      .enable(enable),
      .value(value)
  );
endmodule
