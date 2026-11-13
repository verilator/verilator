// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Case: Assigning to explicit var input port from OUTSIDE (illegal).
// Only 'input var' ports are variable kind (IEEE 1800-2023 23.2.2.3).
// Variable input ports cannot be assigned (IEEE 1800-2023 23.3.3.2).
interface var_if (
    input var logic clk
);
endinterface

// Case: Assigning to net-type input port from INSIDE (illegal).
// Internal assign creates a second driver within the port's own scope.
interface internal_if (
    input wire clk
);
  assign clk = 1'b0;  // ASSIGNIN: internal assign to net input
endinterface

// Case: Driving net-type input port from INSIDE via an instance output.
// Unlike a bind instance, this instance is part of the module's own code.
interface out_if (
    output logic o
);
endinterface

module own_inst (
    input wire i
);
  out_if oif (.o(i));  // ASSIGNIN: own instance drives net input
endmodule

// Case: Driving explicit var input port from a bind instance (illegal).
module var_target (
    input var logic i
);
endmodule

bind var_target out_if oif (.o(i));  // ASSIGNIN: bind instance drives var input

module t;
  logic sig;
  internal_if iif (.clk(sig));
  var_if vif (.clk());
  assign vif.clk = sig;  // ASSIGNIN: external assign to var input
  own_inst u_own (.i(sig));
  var_target u_var (.i());
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
