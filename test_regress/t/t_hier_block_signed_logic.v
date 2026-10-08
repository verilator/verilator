// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  logic signed [31:0] in1 = 3;
  logic signed [31:0] in2 = 4;
  logic signed in_small1 = 1;
  logic signed in_small2 = -1;

  logic signed [31:0] out1;
  logic signed [31:0] out2;
  logic signed out_small1;
  logic signed out_small2;
  int cyc = 0;
  /*verilator lint_off ASCRANGE*/
  logic [2:8] ascending_in = 7'h53;
  /*verilator lint_on ASCRANGE*/
  logic [10:4] descending_in = 7'h2d;
  logic [10:4] descending_out;
  /*verilator lint_off ASCRANGE*/
  logic [2:8] ascending_out;
  /*verilator lint_on ASCRANGE*/
  logic [10:4] descending_out2;
  /*verilator lint_off ASCRANGE*/
  logic [2:8] ascending_out2;
  /*verilator lint_on ASCRANGE*/

  sub sub1 (
      .in(in1),
      .in_small(in_small1),
      .out(out1),
      .out_small(out_small1),
      .ascending_in(ascending_in),
      .descending_out(descending_out),
      .descending_in(descending_in),
      .ascending_out(ascending_out)
  );
  sub sub2 (
      .in(in2),
      .in_small(in_small2),
      .out(out2),
      .out_small(out_small2),
      .ascending_in(ascending_in),
      .descending_out(descending_out2),
      .descending_in(descending_in),
      .ascending_out(ascending_out2)
  );

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    ascending_in <= ascending_in + 7'd3;
    descending_in <= descending_in + 7'd5;
    `checkh(descending_out, {ascending_in[3:8], ascending_in[2]});
    `checkh(ascending_out, {descending_in[4], descending_in[10:5]});
    `checkh(descending_out2, descending_out);
    `checkh(ascending_out2, ascending_out);
    if (out1 == signed'(-3)
            && out2 == signed'(-4)
            && out_small1 == signed'(1'b1)
            && out_small2 == signed'(1'b1)) begin
      if (cyc == 20) begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    end
    else begin
      $write("Mismatch\n");
      $stop;
    end
  end
endmodule

module sub (
    input logic signed [31:0] in,
    input logic signed in_small,
    output logic signed [31:0] out,
    output logic signed out_small,
    /*verilator lint_off ASCRANGE*/
    input logic [2:8] ascending_in,
    /*verilator lint_on ASCRANGE*/
    output logic [10:4] descending_out,
    input logic [10:4] descending_in,
    /*verilator lint_off ASCRANGE*/
    output logic [2:8] ascending_out
    /*verilator lint_on ASCRANGE*/
);  /*verilator hier_block*/
  assign out = -in;
  assign out_small = -in_small;
  assign descending_out = {ascending_in[3:8], ascending_in[2]};
  assign ascending_out = {descending_in[4], descending_in[10:5]};
endmodule
