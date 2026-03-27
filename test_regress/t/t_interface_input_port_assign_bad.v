// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Case 1: Assigning to explicit var input port from OUTSIDE (illegal).
// Only 'input var' ports are variable kind (IEEE 1800-2023 23.2.2.3).
// Variable input ports cannot be assigned (IEEE 1800-2023 23.3.3.2).
interface var_if (
    input var logic clk
);
endinterface

// Case 2: Assigning to net-type input port from INSIDE (illegal).
// Internal assign creates a second driver within the port's own scope.
interface internal_if (
    input wire clk
);
  assign clk = 1'b0;  // ASSIGNIN: internal assign to net input
endinterface

module t;
  logic sig;
  internal_if iif (.clk(sig));
  var_if vif (.clk());
  assign vif.clk = sig;  // ASSIGNIN: external assign to var input
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
