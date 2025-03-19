// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off IMPLICIT

module fifo_v3 #(
    parameter int unsigned DATA_WIDTH = 32,
    parameter int unsigned DEPTH = 8,
    parameter type dtype_t = logic [DATA_WIDTH-1:0]
)(
    input int data_i,
    output int data_o
);
    if (DEPTH == 0) begin : gen_pass_through
    end
endmodule

module axi_lite_mux #(
  parameter int unsigned NoSlvPorts = 32'd32,
  parameter int unsigned MaxTrans = 32'd0
) (
  input logic clk_i,
  input logic rst_ni
);
   wire [31:0] ar_select;
   wire [31:0] r_select;

   if (NoSlvPorts == 32'h1) begin : gen_no_mux
   end
   else begin : gen_mux
      typedef logic [$clog2(NoSlvPorts)-1:0] select_t;
      fifo_v3 #(
                .DEPTH ( MaxTrans ),
                .dtype_t ( select_t )
                )
      i_r_fifo (
                .data_i ( ar_select ),
                .data_o ( r_select )
                );
   end
endmodule

module t
  (
   input logic clk_i,
   input logic rst_ni
   );
   axi_lite_mux i_axi_mux (
                           .clk_i,
                           .rst_ni);
endmodule
