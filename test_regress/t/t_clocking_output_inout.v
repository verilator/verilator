// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Kristof Marien
// SPDX-License-Identifier: CC0-1.0

// Clocking-block outputs driving an inout port must reach the connected net
// for direct, concatenation, part-select and struct assignment pattern
// connections, and for a net shared with another tristate driver.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct packed {
  logic [3:0] hi;
  logic [3:0] lo;
} pair_t;

interface out_if (
    input wire clk,
    inout wire [7:0] bus
);
  clocking cb @(posedge clk);
    default input #1step output #1step;
    output bus;
  endclocking
  task drive(input logic [7:0] value);
    cb.bus <= value;
    @(cb);
  endtask
endinterface

interface inout_if (
    input wire clk,
    inout wire [7:0] bus
);
  clocking cb @(posedge clk);
    default input #1step output #1step;
    inout bus;
  endclocking
  task drive(input logic [7:0] value);
    cb.bus <= value;
    @(cb);
  endtask
endinterface

interface pair_if (
    input wire clk,
    inout wire pair_t bus
);
  clocking cb @(posedge clk);
    default input #1step output #1step;
    output bus;
  endclocking
  task drive(input pair_t value);
    cb.bus <= value;
    @(cb);
  endtask
endinterface

module t;
  logic clk = 0;
  wire [7:0] direct;
  wire [3:0] c_hi, c_lo;
  wire [15:0] wide;
  wire [3:0] p_hi, p_lo;
  wire [7:0] shared;
  logic oe = 1'b0;

  assign shared = oe ? 8'h55 : 'z;

  out_if s_direct (.clk(clk), .bus(direct));
  out_if s_concat (.clk(clk), .bus({c_hi, c_lo}));
  out_if s_sel (.clk(clk), .bus(wide[11:4]));
  pair_if s_pat (.clk(clk), .bus('{hi: p_hi, lo: p_lo}));
  inout_if s_shared (.clk(clk), .bus(shared));

  always #5 clk = ~clk;

  initial begin
    for (int i = 0; i < 4; i++) begin
      fork
        s_direct.drive(8'(8'hA5 + i));
        s_concat.drive(8'(8'h3C + i));
        s_sel.drive(8'(8'h96 + i));
        s_pat.drive(pair_t'(8'(8'h5A + i)));
        s_shared.drive(8'(8'hC3 + i));
      join
      @(posedge clk);
      #1;
      `checkh(direct, 8'(8'hA5 + i));
      `checkh({c_hi, c_lo}, 8'(8'h3C + i));
      `checkh(wide[11:4], 8'(8'h96 + i));
      `checkh({p_hi, p_lo}, 8'(8'h5A + i));
      `checkh(shared, 8'(8'hC3 + i));
      `checkh(s_shared.cb.bus, 8'(8'hC3 + i));
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
