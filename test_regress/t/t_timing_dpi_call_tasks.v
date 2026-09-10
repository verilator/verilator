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
  reg rtl_clk;
  initial begin
    rtl_clk = 1'b0;
    forever #2 rtl_clk = ~rtl_clk;
  end

  task iterate(output int unsigned o);
    for (int n = 0; n < 10; n = n + 1) begin
      @(posedge rtl_clk);
      o = o + 1;
    end
  endtask

  export "DPI-C" task export_nested_suspendable_task;
  task automatic export_nested_suspendable_task(input int unsigned i, output int unsigned o);
    int e = 0;
    iterate(e);
    o = e + i;
  endtask

  export "DPI-C" task export_suspendable_task;
  task automatic export_suspendable_task(input int unsigned i, output int unsigned o);
    @(posedge rtl_clk);
    o = i + 10;
  endtask

  export "DPI-C" task export_nonsuspendable_task;
  task automatic export_nonsuspendable_task(input int unsigned i, output int unsigned o);
    o = i + 10;
  endtask

  import "DPI-C" context task dpi_import1(output int unsigned o);
  import "DPI-C" context task dpi_import2(output int unsigned o);
  import "DPI-C" context task dpi_import3(output int unsigned o);

  integer o = 0;
  initial begin
    dpi_import1(o);
    `checkd(o, 11);
    `checkd($time, 38);

    dpi_import2(o);
    `checkd(o, 12);
    `checkd($time, 42);

    dpi_import3(o);
    `checkd(o, 13);
    `checkd($time, 42);

    $finish;
  end
endmodule
