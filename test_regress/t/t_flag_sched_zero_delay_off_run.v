// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module top;
  int n = 0;
  initial begin
    repeat (5) begin
      #10;
      $display("%02t tick", $time);
      ++n;
      if (n > 5) begin
        #0;  // Will not execute
        $stop;
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
