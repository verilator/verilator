// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;

  // verilog_format: off
  initial begin
    // Too many actuals.
    randsequence(main)
      main : add(1, 2);
      void add(int y) : { $display(y); };
    endsequence

    // Too few actuals (non-defaulted formal).
    randsequence(main)
      main : add();
      void add(int y) : { $display(y); };
    endsequence

    // Named argument with non-existent name.
    randsequence(main)
      main : add(.bogus(1));
      void add(int y) : { $display(y); };
    endsequence

    // Duplicate named argument.
    randsequence(main)
      main : add(.y(1), .y(2));
      void add(int y) : { $display(y); };
    endsequence

    $write("*-* All Finished *-*\n");
    $finish;
  end
  // verilog_format: on

endmodule
