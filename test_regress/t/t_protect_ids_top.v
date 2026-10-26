// DESCRIPTION: Verilator: --protect-ids hides the name of the top module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module secret_top;
  secret_sub secret_inst ();
endmodule

module secret_sub;
  // verilator no_inline_module
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
