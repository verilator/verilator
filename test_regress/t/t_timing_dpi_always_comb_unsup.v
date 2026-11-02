// DESCRIPTION: Verilator: DPI import in always_comb with an unrelated suspendable export
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (input int a, output int b, output int helper_result);
  parameter bit DELAY = 1;
  import "DPI-C" context task dpi_import(input int a, output int b);
  export "DPI-C" task dpi_export;
  task automatic dpi_export();
    if (DELAY) #1;
  endtask

  task automatic shared_import(input int value, output int result);
    /* verilator no_inline_task */
    dpi_import(value, result);
  endtask

  always_comb dpi_import(a, b);
  always_comb shared_import(a, helper_result);
endmodule
