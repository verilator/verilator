// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2015 Iztok Jeras
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t (
    input clk
);

  reg alu_ltu, alu_lts;
  logic [3:0] in_op1;
  logic [3:0] in_op2;


  reg aaa_ltu, aaa_lts;
  always @(posedge clk) begin
    in_op1 = 4'sb1110;
    in_op2 = 4'b0010;
    aaa_ltu = in_op1 < in_op2;
    // bug999
    aaa_lts = $signed(in_op1) < $signed(in_op2);
    `checkh(aaa_ltu, 1'b0);
    `checkh(aaa_lts, 1'b1);
  end

  generate
    if (1) begin
      always @(posedge clk) begin
        in_op1 = 4'sb1110;
        in_op2 = 4'b0010;
        alu_ltu = in_op1 < in_op2;
        // bug999
        alu_lts = $signed(in_op1) < $signed(in_op2);
        `checkh(alu_ltu, 1'b0);
        `checkh(alu_lts, 1'b1);
      end
    end
  endgenerate

  // Issue #9170, extended 1-bit compare must stay unsigned under ~
  int cyc = 0;
  logic [31:0] w;
  logic [31:0] x;
  wire q = {31'b0, &w} < ~{31'b0, (x < w)};
  always @(posedge clk) begin
    cyc <= cyc + 1;
    w <= cyc[0] ? 32'hffffffff : 32'h0;
    x <= 0;
    if (cyc > 2) `checkh(q, 1'b1);
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
