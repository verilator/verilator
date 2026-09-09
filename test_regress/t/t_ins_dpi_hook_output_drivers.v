// DESCRIPTION: Verilator: DPI-hooks on output ports with sequential drivers, drivers that read
// the port back, and a task output argument as driver
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module pass (
    input logic [7:0] i,
    output logic [7:0] o
);
  assign o = i;
endmodule

module sub (
    input logic clk,
    input logic rst,
    input logic [7:0] x,
    output logic [7:0] q_reg,
    output logic [7:0] q_self,
    output logic [7:0] q_arst,
    output logic [7:0] q_task,
    output logic [7:0] q_none,
    output logic [7:0] r_cond,
    output logic [7:0] r_task,
    output logic [7:0] r_pin
);
  task automatic tsk_w(input logic [7:0] a, output logic [7:0] r);
    r = a ^ 8'h0f;
  endtask

  task automatic tsk_r(input logic [7:0] a, output logic [7:0] r);
    r = a + 8'd3;
  endtask

  always @(posedge clk) q_reg <= x;

  always @(posedge clk)
    if (rst) q_self <= 8'h00;
    else q_self <= q_self + 8'd1;

  always @(posedge clk or posedge rst)
    if (rst) q_arst <= 8'h00;
    else q_arst <= q_arst ^ x;

  always_comb tsk_w(x, q_task);

  always_comb
    if (q_reg[0]) r_cond = 8'h11;
    else r_cond = 8'h22;

  always_comb tsk_r(q_reg, r_task);

  pass u_pin (
      .i(q_reg),
      .o(r_pin)
  );
endmodule

module top_module;
  logic clk = 0;
  logic rst = 1;
  int cyc = 0;
  logic [7:0] x;
  logic [7:0] q_reg, q_self, q_arst, q_task, q_none, r_cond, r_task, r_pin;

  assign x = 8'h21 + cyc[7:0] * 8'd5;

  sub u (
      .clk(clk),
      .rst(rst),
      .x(x),
      .q_reg(q_reg),
      .q_self(q_self),
      .q_arst(q_arst),
      .q_task(q_task),
      .q_none(q_none),
      .r_cond(r_cond),
      .r_task(r_task),
      .r_pin(r_pin)
  );

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 0;
    $display("[%0d] reg=%02x self=%02x arst=%02x task=%02x cond=%02x targ=%02x pin=%02x", cyc,
             q_reg, q_self, q_arst, q_task, r_cond, r_task, r_pin);
    if (cyc > 7) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
