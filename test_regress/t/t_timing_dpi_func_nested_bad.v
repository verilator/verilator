// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t ();
  reg clk;
  initial begin
    clk = 1'b0;
    forever #2 clk = ~clk;
  end

  export "DPI-C" task dpi_export_task;
  task dpi_export_task();
    #1;
    $display("%t: dpi_export", $time);
  endtask

  export "DPI-C" function dpi_export_function;
  function int dpi_export_function();
    $display("%t: Calling dpi_import_function2()", $time);
    dpi_export_function = dpi_import_function2();
  endfunction

  import "DPI-C" context function int dpi_import_function1();
  import "DPI-C" context function int dpi_import_function2();

  int n;
  initial begin
    $display("%t: Calling dpi_import_function1()", $time);
    n = dpi_import_function1();
    $finish;
  end
endmodule
