// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Input ports of non-inlined modules with several instances are kept per instance, except
// where that would change what the design sees.

// An input read by an initial block at time zero, also through a hierarchical reference
module reader (
    input [7:0] x,
    output [7:0] y
);
  /*verilator no_inline_module*/
  assign y = x + 8'd1;
  initial `checkh(x, 8'h5a);
endmodule

// An input the module writes itself, so it is the same variable as its connection
module writer (
    input clk,
    input var logic [7:0] i,
    output [7:0] o
);
  /*verilator no_inline_module*/
  assign o = i + 8'd1;
  // verilator lint_off ASSIGNIN
  always @(posedge clk) i <= i + 8'd2;
  // verilator lint_on ASSIGNIN
endmodule

module split_reader (
    input [6:0] x  /*verilator split_var*/,
    output [6:0] y
);
  /*verilator no_inline_module*/
  assign y = x ^ 7'h67;
  initial `checkh(x, 7'h35);
endmodule

module string_reader (
    input string x,
    output string y
);
  /*verilator no_inline_module*/
  assign y = {x, "!"};
  initial `checks(x, "first");
endmodule

module t (
    input clk
);
  int cyc = 0;
  wire [7:0] y1, y2, o1, o2;
  logic [7:0] p1 = 8'h10;
  logic [7:0] p2 = 8'h20;
  logic [7:0] r1 = 8'h5a;
  logic [7:0] r2 = 8'h5a;
  logic [6:0] split_source = 7'h35;
  wire [6:0] split_y1, split_y2;
  string string_source = "first";
  string string_y1, string_y2;

  reader u_r1 (
      .x(r1),
      .y(y1)
  );
  reader u_r2 (
      .x(r2),
      .y(y2)
  );
  initial `checkh(u_r1.x, 8'h5a);
  split_reader u_s1 (
      split_source,
      split_y1
  );
  split_reader u_s2 (
      split_source,
      split_y2
  );
  string_reader u_t1 (
      string_source,
      string_y1
  );
  string_reader u_t2 (
      string_source,
      string_y2
  );

  writer u_w1 (
      .clk(clk),
      .i(p1),
      .o(o1)
  );
  writer u_w2 (
      .clk(clk),
      .i(p2),
      .o(o2)
  );

  always @(posedge clk) begin
    cyc <= cyc + 1;
    r1 <= r1 + 8'd1;
    r2 <= r2 + 8'd2;
    split_source <= split_source + 7'd3;
    string_source <= cyc[0] ? "first" : "next";
    `checkh(split_y1, split_source ^ 7'h67);
    `checkh(split_y2, split_source ^ 7'h67);
    `checks(string_y1, {string_source, "!"});
    `checks(string_y2, {string_source, "!"});
    `checkh(y1, 8'(8'h5b + cyc));
    `checkh(y2, 8'(8'h5b + 2 * cyc));
    // The connected variable follows the writes inside the module
    `checkh(p1, 8'(8'h10 + 2 * cyc));
    `checkh(p2, 8'(8'h20 + 2 * cyc));
    `checkh(o1, 8'(p1 + 1));
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
