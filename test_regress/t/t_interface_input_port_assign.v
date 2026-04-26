// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Driving interface net-type input ports from the instantiating scope is
// legal via both continuous assignment and port connection when port kind
// defaults to net (IEEE 1800-2023 23.2.2.3, 23.3.3.3).

// Scenario 1: bare input (defaults to net)
interface bare_if (
  input clk
);
  logic data;
endinterface

// Scenario 2: input with explicit data type (still net for input)
interface logic_if (
  input logic clk
);
  logic data;
endinterface

// Scenario 3: input with explicit net kind
interface wire_if (
  input wire clk
);
  logic data;
endinterface

module consumer (
  bare_if cif
);
  logic sampled;
  always @(posedge cif.clk) sampled <= cif.data;
endmodule

// Scenario 4: port connection driving interface input (AstPin path)
interface ifc_status (
  input wire busy
);
endinterface

module dut (
  output logic sleep_o
);
  initial sleep_o = 1'b1;
endmodule

module dut_wrap (
  ifc_status sif
);
  dut u_dut (
    .sleep_o(sif.busy)
  );
endmodule

module t;
  logic clk = 0;
  always #5 clk = ~clk;
  integer cyc = 0;

  // Continuous assignment scenarios
  bare_if bif (.clk());
  assign bif.clk = clk;
  assign bif.data = 1'b1;

  logic_if lif (.clk());
  assign lif.clk = clk;
  assign lif.data = 1'b1;

  wire_if wif (.clk());
  assign wif.clk = clk;
  assign wif.data = 1'b1;

  consumer cons (.cif(bif));

  // Port connection scenario
  ifc_status sif (.busy());
  dut_wrap u_wrap (.sif(sif));

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 10) begin
      `checkh(bif.clk, clk);
      `checkh(bif.data, 1'b1);
      `checkh(lif.clk, clk);
      `checkh(lif.data, 1'b1);
      `checkh(wif.clk, clk);
      `checkh(wif.data, 1'b1);
      `checkh(sif.busy, 1'b1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
