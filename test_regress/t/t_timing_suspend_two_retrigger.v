// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module top;

  event a;
  event b;

  initial begin
    #10;
    ->b;
    $display("Sleeping at %0t", $time);
    @(a or b);  // This must wake at due to 'a' from the other block
    $display("Waking   at %0t", $time);
    if ($time != 20) $stop;

    #10;
    ->a;
    ->b;
    $display("Sleeping at %0t", $time);
    @(a or b);  // This must wake at due to 'a' from the other block
    $display("Waking   at %0t", $time);
    if ($time != 40) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

  always begin
    @b;
    #10;
    ->a;
  end

endmodule
