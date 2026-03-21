// DESCRIPTION: Verilator: Verilog Test module
//
// Regression test for virtual interface trigger convergence.
// When combinational logic continuously writes the same value to a virtual
// interface signal (via continuous assign), the VIF trigger must only fire
// on actual value changes. Otherwise, the ICO/NBA scheduling loop never
// converges.
//
// This reproduces the pattern:
//  1. A initial block drived the interface via virtual interface (drv_if)
//  2. A plain interface instance (dut_if) is connected to drv_if via
//     continuous assigns in both directions (request & response)
//  3. Combinational logic (assign) reads from dut_if members and writes
//     response variables back
//  4. Response variables are assigned back to dut_if, which flow to drv_if
//  5. Writing to drv_if fires VIF triggers unconditionally, causing
//     re-evaluation of all VIF-dependent logic in the ICO loop
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Simple bus interface with request and response signals
interface BusIf ();
  logic       req_valid;
  logic       req_ready;
endinterface

module t;

  logic clk = 0;
  int   cyc = 0;

  // Driver interface -- used via virtual interface in class
  BusIf drv_if();

  // DUT interface -- plain interface
  BusIf dut_if();

  // Instantiate virtual interface handle
  virtual BusIf vif = drv_if;

  // --- Bidirectional continuous assigns ---
  // Request direction: drv_if -> dut_if
  assign dut_if.req_valid = drv_if.req_valid;
  // Response direction: dut_if -> drv_if (WRITES TO VIF!)
  assign drv_if.req_ready = 1'b1; // dut_if.req_ready;

  // --- Extract signals from dut_if ---
  logic       ext_valid;
  assign ext_valid = dut_if.req_valid;

  // --- Write response back to dut_if (like AXI_ASSIGN_FROM_RESP) ---
  assign dut_if.req_ready = 1'b1;

  // --- Testbench stimulus using the vif ---
  initial begin
    vif.req_valid = 1'b0;
    @(posedge clk);
    @(posedge clk);
    // These writes to drv_if (VIF) trigger VIF triggers. The response
    // path writes back to drv_if.req_ready with the same value (1'b1),
    // which should NOT re-trigger infinitely.
    vif.req_valid = 1'b1;
    @(posedge clk);
    while (!vif.req_ready) @(posedge clk);
    vif.req_valid = 1'b0;
    @(posedge clk);
    // Send same value again
    vif.req_valid = 1'b1;
    @(posedge clk);
    while (!vif.req_ready) @(posedge clk);
    vif.req_valid = 1'b0;
    @(posedge clk);
    vif.req_valid = 1'b1;
    @(posedge clk);
    while (!vif.req_ready) @(posedge clk);
    vif.req_valid = 1'b0;
    @(posedge clk);
    @(posedge clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial begin
    repeat (30) #5ns clk = ~clk;
  end

endmodule
