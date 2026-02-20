// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
//     Simplified version of config struct to pass params to module
//     hierarchy.  This is a more compact version of the previous
//     example used to debug alongside the interface typedef examples.
//

package a_pkg;
  typedef struct packed {
    int unsigned awidth;
    int unsigned dwidth;
  } cfg_t;
endpackage

module a_mod #(parameter a_pkg::cfg_t cfg=0)(
  input logic a
);
endmodule

module top();
  localparam a_pkg::cfg_t cfg = '{
    awidth : 16
    ,dwidth : 8
  };

  a_mod #(cfg) a_mod_inst(
    .a(1'b0)
  );

  initial begin
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
