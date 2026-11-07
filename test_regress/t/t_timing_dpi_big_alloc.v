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

`define expected_result 1342832650

module t ();
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

  import "DPI-C" context task dpi_import(input int unsigned n, output int unsigned o);

  integer n = 10, o = 0;
  initial begin
    dpi_import(n, o);
    `checkd(o, `expected_result);
    $finish;
  end
endmodule
