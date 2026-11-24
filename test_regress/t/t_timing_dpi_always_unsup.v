// DESCRIPTION: Verilator: DPI imports in always processes with a suspendable export
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (input bit clk, input int a, output int b, output int helper_result,
          output int latch_result, output int star_result, output int ff_result,
          output int loop_result);
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
  always_latch if (a != 0) dpi_import(a, latch_result);
  always @* dpi_import(a, star_result);
  always_ff @(posedge clk) dpi_import(a, ff_result);
  always begin
    dpi_import(a, loop_result);
    #1;
  end
endmodule
