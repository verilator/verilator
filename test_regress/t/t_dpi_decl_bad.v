// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  import "DPI-C" function string func(input string arg)  /*verilator dpi_c_decl*/;

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
