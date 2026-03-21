// DESCRIPTION: Verilator: Verilog Test module
//
// Regression test for virtual interface trigger convergence.
// When combinational logic continuously writes the same value to a virtual
// interface signal (via continuous assign), the VIF trigger must only fire
// on actual value changes. Otherwise, the ICO/NBA scheduling loop never
// converges.
//
// This reproduces the pattern from the AXI bus_compare testbench:
//  1. A DV (driver) interface instance is accessed via virtual interface
//     in a class (drv_if)
//  2. A plain interface instance (dut_if) is connected to drv_if via
//     continuous assigns in both directions (request & response)
//  3. Combinational logic (always_comb) reads from dut_if members (extracted
//     into struct-like variables) and writes response variables back
//  4. Response variables are assigned back to dut_if, which flow to drv_if
//  5. Writing to drv_if fires VIF triggers unconditionally, causing
//     re-evaluation of all VIF-dependent logic in the ICO loop
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Simple bus interface with request and response signals
interface BusIf #(
  parameter int DW = 8
) (
  input logic clk
);
  logic       req_valid;
  logic       req_ready;
  logic [DW-1:0] req_data;
endinterface

// Driver class that holds a virtual interface reference.
// This is what makes drv_if a "virtual interface" in Verilator's eyes.
class Driver #(
  parameter int DW = 8
);
  virtual BusIf #(.DW(DW)) vif;

  function new(virtual BusIf #(.DW(DW)) vif);
    this.vif = vif;
  endfunction

  task reset();
    vif.req_valid <= 1'b0;
    vif.req_data  <= '0;
  endtask

  task send(input logic [DW-1:0] data);
    vif.req_valid <= 1'b1;
    vif.req_data  <= data;
    @(posedge vif.clk);
    while (!vif.req_ready) @(posedge vif.clk);
    vif.req_valid <= 1'b0;
  endtask
endclass

module t;

  logic clk = 0;
  int   cyc = 0;

  // Driver interface (like AXI_BUS_DV) -- used via virtual interface in class
  BusIf #(.DW(8)) drv_if (.clk(clk));

  // DUT interface (like AXI_BUS) -- plain interface
  BusIf #(.DW(8)) dut_if (.clk(clk));

  // Instantiate driver class with virtual interface handle
  Driver #(.DW(8)) drv = new(drv_if);

  // --- Bidirectional continuous assigns (like `AXI_ASSIGN(dut_if, drv_if)) ---
  // Request direction: drv_if -> dut_if
  assign dut_if.req_valid = drv_if.req_valid;
  assign dut_if.req_data  = drv_if.req_data;
  // Response direction: dut_if -> drv_if (WRITES TO VIF!)
  assign drv_if.req_ready = dut_if.req_ready;

  // --- Extract signals from dut_if (like AXI_ASSIGN_TO_REQ) ---
  logic       ext_valid;
  logic [7:0] ext_data;
  assign ext_valid = dut_if.req_valid;
  assign ext_data  = dut_if.req_data;

  // --- Combinational response logic (like always_comb in tb_axi_bus_compare) ---
  logic rsp_ready;
  always_comb begin
    rsp_ready = 1'b1;  // Always accept
  end

  // --- Write response back to dut_if (like AXI_ASSIGN_FROM_RESP) ---
  assign dut_if.req_ready = rsp_ready;

  // --- Testbench stimulus using the driver class ---
  initial begin
    drv.reset();
    @(posedge clk);
    @(posedge clk);
    // These writes to drv_if (VIF) trigger VIF triggers. The response
    // path writes back to drv_if.req_ready with the same value (1'b1),
    // which should NOT re-trigger infinitely.
    drv.send(8'hAB);
    @(posedge clk);
    // Send same value again
    drv.send(8'hAB);
    @(posedge clk);
    drv.send(8'h00);
    @(posedge clk);
    @(posedge clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial begin
    repeat (30) #5ns clk = ~clk;
  end

endmodule
