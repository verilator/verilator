// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   task automatic t;
      // verilator no_inline_task
      string trace;

      $display("== Trace Func");
      trace = $stacktrace();
      if (trace == "") $stop;
      $display("%s", trace);

      $display("== Trace Task");
      $stacktrace;

      $write("*-* All Finished *-*\n");
      $finish;
   endtask

   initial t();

endmodule
