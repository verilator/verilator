// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  reg clk = 1'b1;
  reg reset = 1'b1;

  reg aw_valid = 1'b0;
  reg w_valid = 1'b0;

  reg r_valid;

  reg [31:0] addr[1:0];
  reg [7:0] len[1:0];

  always #5 clk = ~clk;

  initial begin
    #5;  // Align with negedge clk

    #20;
    `checkh(addr[0], 32'h0000_0000);
    reset = 1'b0;

    #20;
    `checkh(addr[0], 32'h0000_0000);
    aw_valid = 1'b1;
    w_valid = 1'b1;

    #10;
    `checkh(addr[0], 32'h4444_4444);
    aw_valid = 1'b0;

    #10;
    `checkh(addr[0], 32'h2222_2222);
    w_valid = 1'b0;

    #10;
    `checkh(addr[0], 32'h2222_2222);
    $write("*-* All Finished *-*\n");
    $finish;
  end


  always @(posedge clk) begin
    if (reset) begin
      r_valid <= 0;
      addr[0] <= '0;
    end
    else begin
      if (r_valid) begin
        addr[0] <= 32'h11111111;
        len[0] <= len[0] - 1;
      end
      if (w_valid) begin
        addr[0] <= 32'h22222222;
      end
      if (aw_valid) begin
        addr[0] <= 32'h33333333;
        len[0] <= 8'hff;
        if (w_valid) addr[0] <= 32'h44444444;
      end
    end
  end

  // Written after time 0, so not a constant, and the arrays below are not split into elements
  int idx;
  initial #1 idx = 0;

  // Consecutive NBAs do not share a flag when updating an array of another scope
  sub u_sub ();
  always @(posedge clk) begin
    u_sub.arr[idx] <= 8'h01;
    u_sub.arr[idx+1] <= 8'h02;
  end
  initial begin
    #12;
    `checkh(u_sub.arr[0], 8'h01);
    `checkh(u_sub.arr[1], 8'h02);
  end

  // Nor when updating arrays also updated on different clocks
  reg [7:0] c[2];
  // verilator lint_off MULTIDRIVEN
  reg [7:0] d[2];
  // verilator lint_on MULTIDRIVEN
  always @(posedge clk) begin
    // The 'if' depends on a variable written in the process, so is not split by array
    bit en;
    en = idx == 0;
    if (en) begin
      c[idx] <= 8'h03;
      d[idx] <= 8'h04;
    end
  end
  always @(negedge clk) d[idx+1] <= 8'h05;
  initial begin
    #12;
    `checkh(c[0], 8'h03);
    `checkh(d[0], 8'h04);
    `checkh(d[1], 8'h05);
  end
endmodule

module sub;
  // verilator no_inline_module
  reg [7:0] arr[2];
endmodule
