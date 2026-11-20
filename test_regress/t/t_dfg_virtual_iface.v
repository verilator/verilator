// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface inner_if;
  logic [6:0] x = 0;
  logic [6:0] y;
  assign y = x + 7'd1;
endinterface

interface bus_if (
    input logic clk
);
  logic [6:0] data = 0;
  logic [6:0] data_p1;
  logic [6:0] acc = 0;
  logic [6:0] sum;
  logic [6:0] mixed;
  inner_if in ();
  assign data_p1 = data + 7'd1;
  assign sum = acc + 7'd3;
  assign mixed = sum ^ 7'h5a;
  always @(posedge clk) acc <= mixed;
  function void set_x(logic [6:0] v);
    in.x = v;
  endfunction
endinterface

module t;
  logic clk = 0;
  always #5 clk = ~clk;
  bus_if b1 (clk), b2 (clk);
  virtual bus_if v;
  initial begin
    v = b1;
    for (int i = 1; i <= 3; ++i) begin
      // Written through the virtual interface
      v.data = 7'(10 * i);
      // Written by a function called through the virtual interface
      v.set_x(7'(20 * i));
      @(posedge clk);
      #1;
      `checkh(b1.data_p1, 7'(10 * i + 1));
      `checkh(b1.in.y, 7'(20 * i + 1));
      `checkh(b2.data_p1, 7'd1);
      `checkh(b2.in.y, 7'd1);
    end
    `checkh(b1.acc, 7'd83);
    `checkh(b2.acc, 7'd83);
    // Read through the virtual interface
    `checkh(v.sum, 7'd86);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
