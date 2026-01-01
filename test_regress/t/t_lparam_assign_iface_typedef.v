// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
//     assign localparam from interface typedef, single level nesting

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0h exp=%0h\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface x_if #(
  parameter int p_awidth = 4,
  parameter int p_dwidth = 7
)();
  typedef struct packed {
    logic [p_awidth-1:0] addr;
    logic [p_dwidth-1:0] data;
  } rq_t;

  typedef struct packed {
    logic [p_dwidth-1:0] data;
  } rs_t;
endinterface

module top();
  x_if #(
    .p_awidth(16),
    .p_dwidth(8)
  ) if0();

  localparam p0_rq_t = if0.rq_t;
  localparam p0_rs_t = if0.rs_t;

  p0_rq_t rq;
  p0_rs_t rs;

  always_comb begin
    rq.addr = 'h1234;
    rq.data = 'h37;
    rs.data = 'h5a;
  end

  initial begin
    #1;
    `checkh(rq.addr, 16'h1234);
    `checkh(rq.data, 8'h37);
    `checkh(rs.data, 8'h5a);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
