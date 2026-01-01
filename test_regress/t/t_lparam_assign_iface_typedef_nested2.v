// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
//     assign localparam from nested interface typedef
//     instance of type, assign to instance and check
//

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0h exp=%0h\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface y_if #(
    parameter int p_awidth = 3
) ();
  typedef struct packed {logic [p_awidth-1:0] addr;} rq2_t;
endinterface

interface x_if #(
    parameter int p_awidth = 4,
    parameter int p_dwidth = 7
) ();
  typedef struct packed {
    logic [p_awidth-1:0] addr;
    logic [p_dwidth-1:0] data;
  } rq_t;

  typedef struct packed {logic [p_dwidth-1:0] data;} rs_t;

  y_if #(.p_awidth(p_awidth)) y_if0 ();
endinterface

module top ();
  x_if #(
      .p_awidth(16),
      .p_dwidth(8)
  ) if0 ();

  localparam p0_rq2_t = if0.y_if0.rq2_t;

  p0_rq2_t p0_rq2;

  assign p0_rq2.addr = 16'hcafe;

  initial begin
    #1;
    `checkh(p0_rq2.addr, 16'hcafe);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
