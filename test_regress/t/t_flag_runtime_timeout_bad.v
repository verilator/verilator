// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    $display("Sleeping....");
    $system("sleep 20");
    $display("%%Error: Sleep done (should have timed out)....");
    $stop;
  end
endmodule
