// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//

interface x_if #(
    parameter int a_width = 3
) ();

  typedef struct packed {logic [a_width-1:0] addr;} rq_t;
endinterface

module top ();
  x_if #(.a_width(8)) if0 ();

  localparam type p0_t = if0.rq_t;

  initial begin
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
