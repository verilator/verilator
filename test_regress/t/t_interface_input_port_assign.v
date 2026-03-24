// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Driving interface input ports from the instantiating scope via
// continuous assign is legal (IEEE 1800-2023 25.4).

interface clk_if (input logic clk);
  logic data;
endinterface

interface bus_if #(parameter WIDTH = 8) (input logic clk, input logic rst_n);
  logic [WIDTH-1:0] wdata;
endinterface

module consumer (clk_if cif);
  logic sampled;
  always @(posedge cif.clk) sampled <= cif.data;
endmodule

module t (/*AUTOARG*/
  // Inputs
  clk
);
  input clk;
  integer cyc = 0;

  logic rst_n = 0;

  // Scenario 1: Single input port driven via assign
  clk_if cif(.clk());
  assign cif.clk = clk;

  // Scenario 2: Multiple input ports, parameterized interface
  bus_if #(.WIDTH(16)) bif(.clk(), .rst_n());
  assign bif.clk = clk;
  assign bif.rst_n = rst_n;

  // Scenario 3: Non-port signals driven (always legal)
  assign cif.data = 1'b1;
  assign bif.wdata = 16'hBEEF;

  consumer cons(.cif(cif));

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) rst_n <= 1'b1;
    if (cyc == 10) begin
      `checkh(cif.clk, clk);
      `checkh(bif.rst_n, 1'b1);
      `checkh(bif.wdata, 16'hBEEF);
      `checkh(cif.data, 1'b1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
