// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
//     Chained typedef aliases from an interface typedef

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0h exp=%0h\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface x_if #(
    parameter int p_awidth = 4
) ();
  typedef struct packed {logic [p_awidth-1:0] addr;} rq_t;
endinterface

module top ();
  x_if #(.p_awidth(16)) if0 ();

  // First alias of interface typedef
  typedef if0.rq_t my_rq_t;
  // Second alias of the alias
  typedef my_rq_t my_rq2_t;

  my_rq2_t rq;

  always_comb begin
    rq.addr = 'h1234;
  end

  initial begin
    #1;
    `checkh(rq.addr, 16'h1234);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
