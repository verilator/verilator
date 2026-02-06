// DESCRIPTION: Verilator: Test non-constant interface array loop index error
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

interface simple_bad_if;
  logic [7:0] value;
endinterface

module t (/*AUTOARG*/
  // Inputs
  clk
);

  input clk;

  localparam N = 4;

  simple_bad_if ifaces [N-1:0] ();

  // BAD: Loop with runtime-variable bound - not unrollable, so the
  // interface array index cannot be resolved to a constant.
  logic [7:0] limit;
  always_comb begin
    for (int i = 0; i < limit; i++) begin
      ifaces[i].value = 8'(i);
    end
  end

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
