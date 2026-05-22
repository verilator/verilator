// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module dpi_test ();

  reg rtl_clk;
  initial begin
    rtl_clk = 1'b0;
    forever #2 rtl_clk = ~rtl_clk;
  end


  export "DPI-C" dpi_export = task dpi_export;
  task dpi_export(input int unsigned i);
    @(posedge rtl_clk);
    $display("%t: dpi_export: i=%3d", $time, i);
  endtask

  import "DPI-C" context task dpi_import(input int unsigned n);

  integer n = 10;
  initial begin
    dpi_import(n);
    $finish;
  end
endmodule
