// DESCRIPTION: Verilator: DPI import in always @* with an unrelated suspendable export
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (input bit clk, input int a, output int b, output int c, output int d);
  parameter bit DELAY = 1;
  import "DPI-C" context task dpi_import(input int a, output int b);
  export "DPI-C" task dpi_export;
  task automatic dpi_export();
    if (DELAY) #1;
  endtask

  always @* dpi_import(a, b);
  always_ff @(posedge clk) dpi_import(a, c);
  always begin
    dpi_import(a, d);
    #1;
  end
endmodule
