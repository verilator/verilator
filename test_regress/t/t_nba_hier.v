// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  logic clk = 1'b0;
  always #5 clk = ~clk;

  logic [7:0] x;

  sub a_0 ();
  sub a_1 ();
  always @(posedge clk) begin
    a_0.x[3:0] <= ~x[3:0];
    a_1.x[7:0] <= ~x;
  end

  sub b_0 ();
  sub b_1 ();
  always begin
    // Having this @posedge here makes this a 'suspendable' process, causing
    // the use of the FlagUnique scheme
    @(posedge clk);
    b_0.x[3:0] <= ~x[3:0];
    b_1.x[7:0] <= ~x;
  end

  sub c_0 ();
  sub c_1 ();
  always @(posedge clk) begin
    c_0.x[3:0] <= ~x[3:0];
    c_1.x[7:0] <= ~x;
  end
  assign c_0.x[9:8] = 2'd1;
  assign c_1.x[9:8] = 2'd2;

  sub d_0 ();
  sub d_1 ();
  always @(posedge clk) begin
    d_0.y[0][3:0] <= ~x[3:0];
    d_1.y[0][7:0] <= ~x;
  end

  sub e_0 ();
  sub e_1 ();
  always @(posedge clk) begin
    for (int i = 0; i < 2; ++i) begin
      e_0.y[i][3:0] <= ~x[3:0];
      e_1.y[i][7:0] <= ~x;
    end
  end

  initial begin
    #1;
    x = 8'hcc;
    @(posedge clk);
    @(negedge clk);
    `checkh(a_0.x[3:0], 4'h3);
    `checkh(a_1.x[7:0], 8'h33);
    `checkh(b_0.x[3:0], 4'h3);
    `checkh(b_1.x[7:0], 8'h33);
    `checkh(c_0.x[3:0], 4'h3);
    `checkh(c_0.x[9:8], 2'h1);
    `checkh(c_1.x[7:0], 8'h33);
    `checkh(c_1.x[9:8], 2'h2);
    `checkh(d_0.y[0][3:0], 4'h3);
    `checkh(d_1.y[0][7:0], 8'h33);
    for (int i = 0; i < 2; ++i) begin
      `checkh(e_0.y[i][3:0], 4'h3);
      `checkh(e_1.y[i][7:0], 8'h33);
    end

    #1;
    x = 8'h55;
    @(posedge clk);
    @(negedge clk);
    `checkh(a_0.x[3:0], 4'ha);
    `checkh(a_1.x[7:0], 8'haa);
    `checkh(b_0.x[3:0], 4'ha);
    `checkh(b_1.x[7:0], 8'haa);
    `checkh(c_0.x[3:0], 4'ha);
    `checkh(c_0.x[9:8], 2'h1);
    `checkh(c_1.x[7:0], 8'haa);
    `checkh(c_1.x[9:8], 2'h2);
    `checkh(d_0.y[0][3:0], 4'ha);
    `checkh(d_1.y[0][7:0], 8'haa);
    for (int i = 0; i < 2; ++i) begin
      `checkh(e_0.y[i][3:0], 4'ha);
      `checkh(e_1.y[i][7:0], 8'haa);
    end

    #1;
    $finish;
  end

endmodule

module sub;
  logic [9:0] x;
  logic [9:0] y[99];
endmodule
