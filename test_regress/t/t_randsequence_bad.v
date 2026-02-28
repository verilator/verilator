// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;

  initial begin;
    randsequence(no_such_production)  // Bad
      such_production: { };
    endsequence

    randsequence(main)
      main: production_bad;  // Bad
      production_baa: {};
    endsequence

    randsequence()
      duplicated_bad: { $display("dup1"); };
      duplicated_bad: { $display("dup2"); };  // Bad
    endsequence

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
