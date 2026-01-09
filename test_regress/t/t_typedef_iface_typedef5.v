// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
//     assign localparam from interface typedef, single level nesting

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0h exp=%0h\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface x_if #(
    parameter int p_awidth = 4
) ();
  typedef struct packed {logic [p_awidth-1:0] addr;} rq_t;
endinterface

interface y_if #(
    parameter int p_dwidth = 7
) ();
  typedef struct packed {logic [p_dwidth-1:0] data;} rs_t;
endinterface

interface z_if #(
    parameter int p_awidth = 3,
    parameter int p_dwidth = 9
);
  x_if #(p_awidth) x_if0 ();
  y_if #(p_dwidth) y_if0 ();
endinterface

module top ();
  z_if #(
      .p_awidth(16),
      .p_dwidth(8)
  ) if0 ();

  typedef if0.x_if0.rq_t rq_t;
  typedef if0.y_if0.rs_t rs_t;

  rq_t rq;
  rs_t rs;

  always_comb begin
    rq.addr = 'h1234;
    rs.data = 'ha5;
  end

  initial begin
    #1;
    `checkh(rq.addr, 16'h1234);
    `checkh(rs.data, 8'ha5);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
