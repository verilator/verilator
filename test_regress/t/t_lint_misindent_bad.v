// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Do not reindent - spaces are critical to this test

// verilator lint_off UNUSEDLOOP

module t (/*AUTOARG*/);

   initial begin
      if (0)
        $display("ok");
        $display("bad1");  // <--- Bad

      if (0)
        $display("ok");
      else
        $display("ok");
        $display("bad2");  // <--- Bad

      for (;0;)
        $display("ok");
        $display("bad3");  // <--- Bad

      while (0)
        $display("ok");
        $display("bad4");  // <--- Bad

      // Normal styles
      if (0) $display("ok");
      $display("ok");
      for (;0;) $display("ok");
      $display("ok");
      while (0) $display("ok");
      $display("ok");

      // Questionable but pops up in some cases e.g. SweRV
      // (all statements have similar indent)
      if (0)
        begin
          $display("ok");
        end
          $display("ok");

   end

endmodule
