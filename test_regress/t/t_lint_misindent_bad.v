// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Do not reindent - spaces are critical to this test
// verilog_format: off
// verilator lint_off UNUSEDLOOP

module t;

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

    // A loop as a fork branch, followed by the next branch
    fork
      for (;0;)
        $display("ok");
        $display("bad5");  // <--- Bad
      while (0)
        $display("ok");
        $display("bad6");  // <--- Bad
    join

    // An end starting its line, with a statement run on after it
    // and the following line indented as if inside an else
    if (0) begin
      $display("ok");
    end case (1'b0)
      1'b1: $display("bad7");  // <--- Bad (case after end)
      default: ;
    endcase

    if (0) begin
      $display("ok");
    end begin
      $display("bad8");  // <--- Bad (begin after end)
    end

    if (0) begin
      $display("ok");
    end $display("ok");
      $display("bad9");  // <--- Bad (statement after end)

    if (0) begin
      $display("ok");
    end for (int i = 0; i < 1; ++i)
      $display("bad10");  // <--- Bad (loop after end, one warning)

    // Blank line after run-on statement might be misleading but
    // leads to false positives
    if (0) begin
      $display("ok");
    end $display("ok");

      $display("ok");

    // Run-on lines, or a following line not indented, are not misleading
    if (0) begin $display("ok"); end case (1'b0)
      1'b1: $display("ok");
      default: ;
    endcase
    if (0) begin
      $display("ok");
    end $display("ok");
    $display("ok");
    if (0) begin $display("ok"); end $display("ok");

  end

endmodule
