// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module sub #(
  parameter int SUB_PARAM = 7
) ();

  localparam int SUB_LOCALPARAM = 3;
  int by_pragma /*verilator public_flat_rd*/;
  int by_vlt;
  int not_public;

  initial begin
    by_pragma  = SUB_PARAM;
    by_vlt     = SUB_LOCALPARAM;
    not_public = 0;
  end

endmodule

module top();
  sub i_sub();

  initial begin
    $c("Verilated::scopesDump();");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
