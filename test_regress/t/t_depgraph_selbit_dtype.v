// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//

// Test for COND node dtype not being set when using type parameters
// This reproduces the issue from spill_register_flushable.sv:95
// The issue involves type parameters used in ternary expressions
// Key: T defaults to logic, and a COND expression uses variables of type T

// Spill register with type parameter (simplified from spill_register_flushable)
module spill_register #(
  parameter type T = logic
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic sel_i,
  input  T     data_i,
  output T     data_o
);
  // Two registers of type T
  T a_data_q;
  T b_data_q;
  logic b_full_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
          a_data_q <= '0;
          b_data_q <= '0;
          b_full_q <= 1'b0;
      end else begin
          a_data_q <= data_i;
          b_data_q <= a_data_q;
          b_full_q <= sel_i;
      end
  end

  // This is the problematic line - ternary expression with type parameter variables
  // The COND node's dtype should be T, but it's not being set
  assign data_o = b_full_q ? b_data_q : a_data_q;
endmodule

// Wrapper module that passes type parameter through (like spill_register_flushable wrapper)
module spill_wrapper #(
  parameter type T = logic
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic sel_i,
  input  T     data_i,
  output T     data_o
);
  // Instantiate spill_register with the same type parameter
  spill_register #(.T(T)) i_spill (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .sel_i(sel_i),
    .data_i(data_i),
    .data_o(data_o)
  );
endmodule

// Another level of nesting (like axi_demux)
module demux #(
  parameter type T = logic
) (
  input  logic clk_i,
  input  logic rst_ni
);
  logic sel;
  T data_in;
  T data_out;

  spill_wrapper #(.T(T)) i_spill_wrapper (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .sel_i(sel),
    .data_i(data_in),
    .data_o(data_out)
  );
endmodule

module top;
  logic clk;
  logic rst_n;

  // Instantiate with default T (logic)
  demux #(.T(logic)) u_demux (
    .clk_i(clk),
    .rst_ni(rst_n)
  );

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
