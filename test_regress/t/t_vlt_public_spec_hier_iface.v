// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0


interface ifc();
  logic [7:0] data;
endinterface

module top();
  ifc i_single ();
  ifc i_arr [2:0] ();
  ifc i_md [1:0][1:0] ();

  initial begin
    $c("Verilated::scopesDump();");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
