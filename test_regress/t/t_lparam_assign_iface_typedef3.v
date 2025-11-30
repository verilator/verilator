// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
//     assign localparam from interface typedef, single level nesting
//

interface x_if #(
  parameter int p_awidth = 4
  ,parameter int p_dwidth = 7
)();
  typedef struct packed {
    logic [p_awidth-1:0] addr;
    logic [p_dwidth-1:0] data;
  } rq_t;
endinterface

module top();
  x_if #(
    .p_awidth(16)
    ,.p_dwidth(8)
  ) if0 [2]();

  localparam type p0_rq_t = if0[0].rq_t;

  p0_rq_t rq;

  always_comb begin
    rq.addr = 'h1234;
    rq.data = 'h37;
  end

  initial begin
    #1;
    if(rq.addr != 16'h1234) $stop;
    if(rq.data != 8'h37) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
