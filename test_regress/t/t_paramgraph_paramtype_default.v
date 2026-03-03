// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//

// DESCRIPTION: Verilator: Test for REQUIREDTYPE resolution with default type parameters
//
// This test verifies that modules with `parameter type T = logic` work correctly
// when instantiated WITHOUT overriding the type parameter (using the default).
//

// Simple type flop - parameterized by type T with default = logic
module tflop #(parameter type T = logic) (
  input logic clk,
  input logic reset,
  input T reset_strap_i,
  output T q_o,
  input T d_i
);
  always_ff @(posedge clk) begin
    if (reset) begin
      q_o <= reset_strap_i;
    end else begin
      q_o <= d_i;
    end
  end
endmodule

// Module that uses tflop with DEFAULT type parameter (T = logic)
module user_mod (
  input logic clk,
  input logic reset
);
  logic d_in, d_out;

  // Use tflop with default type parameter T = logic
  // This should NOT create a specialized clone - it reuses the template
  tflop vld_reg (
    .clk(clk),
    .reset(reset),
    .reset_strap_i(1'b0),
    .q_o(d_out),
    .d_i(d_in)
  );

  initial begin
    d_in = 1'b1;
    #10;
    $display("d_out = %b", d_out);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module t;
  logic clk = 0;
  logic reset = 1;

  user_mod uut (.clk(clk), .reset(reset));

  initial begin
    #5 reset = 0;
    #10 clk = 1;
    #10 clk = 0;
    #10 $finish;
  end
endmodule
