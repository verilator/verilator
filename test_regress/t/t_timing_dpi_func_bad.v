// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t ();
  bit completed = 0;
  reg clk;
  initial begin
    clk = 1'b0;
    forever #2 clk = ~clk;
  end

  export "DPI-C" dpi_export_task = task dpi_export_task;
  task dpi_export_task();
    #1;
  endtask

  export "DPI-C" dpi_export_func = function dpi_export_func;
  function void dpi_export_func();
    completed = 1;
  endfunction

  import "DPI-C" context function int dpi_import_calls_task();
  import "DPI-C" context function int dpi_import_calls_func();

  integer n;
  initial begin
    $display("%t: calling dpi_import_function", $time);
    n = dpi_import_calls_func();
    if (completed == 0) `stop;
    $display("%t: calling dpi_import_task", $time);
    n = dpi_import_calls_task();
    $finish;
  end
endmodule
