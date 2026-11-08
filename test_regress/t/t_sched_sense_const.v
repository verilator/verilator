// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Change sensitivity on a constant driven net fires once at time 0, as the
// continuous assignment is evaluated at time 0, whether or not the process
// can suspend. So does an edge of its LSB that the constant has then, and
// any other edge never fires.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module sub #(
    parameter P = 0
) (
    output [5:0] o
);
  assign o = P;
endmodule

module t;
  bit never;

  wire [5:0] w_const;
  assign w_const = 6'd32;
  logic [5:0] a_const_n = 1;
  logic [5:0] a_const_s = 1;
  int cnt_const_n = 0;
  int cnt_const_s = 0;
  always @(w_const) begin
    cnt_const_n++;
    a_const_n <= w_const;
  end
  always @(w_const) begin
    cnt_const_s++;
    a_const_s <= w_const;
    if (never) #1;
  end

  localparam P = 4;
  wire [5:0] w_param = (P == 4) ? 6'd32 : 6'd8;
  logic [5:0] a_param_n = 1;
  logic [5:0] a_param_s = 1;
  int cnt_param_n = 0;
  int cnt_param_s = 0;
  always @(w_param) begin
    cnt_param_n++;
    a_param_n <= w_param;
  end
  always @(w_param) begin
    cnt_param_s++;
    a_param_s <= w_param;
    if (never) #1;
  end

  wire [5:0] w_port;
  sub #(.P(32)) u_sub (.o(w_port));
  logic [5:0] a_port_n = 1;
  logic [5:0] a_port_s = 1;
  int cnt_port_n = 0;
  int cnt_port_s = 0;
  always @(w_port) begin
    cnt_port_n++;
    a_port_n <= w_port;
  end
  always @(w_port) begin
    cnt_port_s++;
    a_port_s <= w_port;
    if (never) #1;
  end

  wire [5:0] w_odd = 6'd33;
  wire [5:0] w_even = 6'd32;
  int cnt_pos_odd_n = 0;
  int cnt_pos_odd_s = 0;
  int cnt_neg_even_n = 0;
  int cnt_neg_even_s = 0;
  int cnt_pos_even_n = 0;
  int cnt_pos_even_s = 0;
  int cnt_neg_odd_n = 0;
  int cnt_neg_odd_s = 0;
  always @(posedge w_odd) cnt_pos_odd_n++;
  always @(posedge w_odd) begin
    cnt_pos_odd_s++;
    if (never) #1;
  end
  always @(negedge w_even) cnt_neg_even_n++;
  always @(negedge w_even) begin
    cnt_neg_even_s++;
    if (never) #1;
  end
  always @(posedge w_even) cnt_pos_even_n++;
  always @(posedge w_even) begin
    cnt_pos_even_s++;
    if (never) #1;
  end
  always @(negedge w_odd) cnt_neg_odd_n++;
  always @(negedge w_odd) begin
    cnt_neg_odd_s++;
    if (never) #1;
  end

  initial begin
    #1;
    `checkd(cnt_const_n, 1);
    `checkd(cnt_const_s, 1);
    `checkd(a_const_n, 32);
    `checkd(a_const_s, 32);
    `checkd(cnt_param_n, 1);
    `checkd(cnt_param_s, 1);
    `checkd(a_param_n, 32);
    `checkd(a_param_s, 32);
    `checkd(cnt_port_n, 1);
    `checkd(cnt_port_s, 1);
    `checkd(a_port_n, 32);
    `checkd(a_port_s, 32);
    `checkd(cnt_pos_odd_n, 1);
    `checkd(cnt_pos_odd_s, 1);
    `checkd(cnt_neg_even_n, 1);
    `checkd(cnt_neg_even_s, 1);
    `checkd(cnt_pos_even_n, 0);
    `checkd(cnt_pos_even_s, 0);
    `checkd(cnt_neg_odd_n, 0);
    `checkd(cnt_neg_odd_s, 0);
    #10;
    `checkd(cnt_const_n, 1);
    `checkd(cnt_const_s, 1);
    `checkd(cnt_param_n, 1);
    `checkd(cnt_param_s, 1);
    `checkd(cnt_port_n, 1);
    `checkd(cnt_port_s, 1);
    `checkd(cnt_pos_odd_n, 1);
    `checkd(cnt_pos_odd_s, 1);
    `checkd(cnt_neg_even_n, 1);
    `checkd(cnt_neg_even_s, 1);
    `checkd(cnt_pos_even_n, 0);
    `checkd(cnt_pos_even_s, 0);
    `checkd(cnt_neg_odd_n, 0);
    `checkd(cnt_neg_odd_s, 0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
