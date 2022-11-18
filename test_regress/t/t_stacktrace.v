// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   task t;
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
