// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`ifdef LIB_CREATE
// This is built with --lib-create. The ports have different sizes, so ordering
// variables for layout would reorder them.

module sub (
    input logic [62:0] wide,
    input logic clk,
    input logic [6:0] narrow,
    output logic [30:0] sum,
    output logic flag,
    /*verilator lint_off ASCRANGE*/
    input logic [2:8] ascending_in,
    /*verilator lint_on ASCRANGE*/
    output logic [10:4] descending_out,
    input logic [10:4] descending_in,
    /*verilator lint_off ASCRANGE*/
    output logic [2:8] ascending_out
    /*verilator lint_on ASCRANGE*/
);

  always_ff @(posedge clk) begin
    sum <= wide[30:0] + {24'd0, narrow};
    flag <= ^wide;
    descending_out <= {ascending_in[3:8], ascending_in[2]};
    ascending_out <= {descending_in[4], descending_in[10:5]};
  end

endmodule

`else
// This is built as the top level

module top;

  logic clk = 1'b0;
  int cyc = 0;
  logic [62:0] wide = 63'h01234567_89abcdef;
  logic [6:0] narrow = 7'h5a;
  logic [30:0] sum;
  logic flag;
  logic [30:0] exp_sum;
  logic exp_flag;
  /*verilator lint_off ASCRANGE*/
  logic [2:8] ascending_in = 7'h53;
  /*verilator lint_on ASCRANGE*/
  logic [10:4] descending_in = 7'h2d;
  logic [10:4] descending_out;
  /*verilator lint_off ASCRANGE*/
  logic [2:8] ascending_out;
  /*verilator lint_on ASCRANGE*/
  logic [10:4] exp_descending_out;
  /*verilator lint_off ASCRANGE*/
  logic [2:8] exp_ascending_out;
  /*verilator lint_on ASCRANGE*/

  always #5 clk = ~clk;

  // Positional connections need the library wrapper to keep the source port order
  sub sub_i (
      wide,
      clk,
      narrow,
      sum,
      flag,
      ascending_in,
      descending_out,
      descending_in,
      ascending_out
  );

  // Whole-vector transfers can hide reversed ranges; inspect the wrapper ports directly.
  initial begin
    `checkh($left(sub_i.ascending_in), 2);
    `checkh($right(sub_i.ascending_in), 8);
    `checkh($left(sub_i.ascending_out), 2);
    `checkh($right(sub_i.ascending_out), 8);
    `checkh($left(sub_i.descending_in), 10);
    `checkh($right(sub_i.descending_in), 4);
    `checkh($left(sub_i.descending_out), 10);
    `checkh($right(sub_i.descending_out), 4);
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    wide <= {wide[61:0], wide[62] ^ wide[61]};
    narrow <= narrow + 7'd3;
    exp_sum <= wide[30:0] + {24'd0, narrow};
    exp_flag <= ^wide;
    ascending_in <= ascending_in + 7'd3;
    descending_in <= descending_in + 7'd5;
    exp_descending_out <= {ascending_in[3:8], ascending_in[2]};
    exp_ascending_out <= {descending_in[4], descending_in[10:5]};
  end

  always @(negedge clk) begin
    if (cyc > 0) begin
      `checkh(sum, exp_sum);
      `checkh(flag, exp_flag);
      `checkh(descending_out, exp_descending_out);
      `checkh(ascending_out, exp_ascending_out);
    end
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

`endif
