// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// Test to assert that property argument type is not retained from
// the previous variable and is not causing errors

module t (
    input clk
);
  genvar i;
  property prop(prop_arg);
    @(posedge clk) (prop_arg |-> prop_arg);
  endproperty

  wire w;
  property prop2(prop_arg);
    @(posedge clk) (prop_arg |-> prop_arg);
  endproperty

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
