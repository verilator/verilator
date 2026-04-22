// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module dpi_test ();

  reg clk;
  initial begin
    clk = 1'b0;
    forever #2 clk = ~clk;
  end

  export "DPI-C" dpi_export = task dpi_export;
  task dpi_export();
    #1;
    $display("%t: dpi_export", $time);
  endtask

  import "DPI-C" context function int dpi_import();

  integer n;
  initial begin
    $display("%t: calling dpi_import", $time);
    n = dpi_import();
    $finish;
  end
endmodule
