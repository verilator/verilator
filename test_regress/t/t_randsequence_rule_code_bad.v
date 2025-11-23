// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2025 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;

  initial begin
    randsequence()
      main : first := 1 { $stop; } | second := 0;
      first : { $display("first"); };
      second : { $display("second"); };
    endsequence
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
