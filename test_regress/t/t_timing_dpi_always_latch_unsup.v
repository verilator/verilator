// DESCRIPTION: Verilator: DPI import in always_latch with an unrelated suspendable export
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (input int a, output int b);
  parameter bit DELAY = 1;
  import "DPI-C" context task dpi_import(input int a, output int b);
  export "DPI-C" task dpi_export;
  task automatic dpi_export();
    if (DELAY) #1;
  endtask

  always_latch if (a != 0) dpi_import(a, b);
endmodule
