// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
//     assign localparam from nested interface typedef
//

interface x_if #(
  parameter int p_awidth = 4
)();
  typedef struct packed {
    logic [p_awidth-1:0] addr;
  } rq_t;
endinterface

interface y_if #(
  parameter int p_dwidth = 7
)();
  typedef struct packed {
    logic [p_dwidth-1:0] data;
  } rs_t;
endinterface

interface z_if #(
  parameter int p_awidth = 3,
  parameter int p_dwidth = 9
);
  x_if #(p_awidth) x_if0();
  y_if #(p_dwidth) y_if0();
endinterface

module top();

  z_if #(.p_awidth(16) ,.p_dwidth(8)) if0();

  localparam type rq_t = if0.x_if0.rq_t;

  rq_t rq;

  initial begin
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
