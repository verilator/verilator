// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Assigning to an interface input port from INSIDE the interface is illegal.

interface bad_if (input logic clk);
  assign clk = 1'b0;  // ASSIGNIN error expected
endinterface

module t;
  logic sig;
  bad_if bif(.clk(sig));
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
