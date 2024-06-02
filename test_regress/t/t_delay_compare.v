// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   int tim1;
   int tim2;
   real rtim1;
   real rtim2;

   initial begin
      tim1 = 2;
      tim2 = 3;
      // verilator lint_off WIDTHEXPAND
      # (tim1 < tim2);
      // verilator lint_on WIDTHEXPAND
      if ($time != 1) $stop;

      // verilator lint_off WIDTHEXPAND
      # (tim1);
      // verilator lint_on WIDTHEXPAND
      if ($time != 1 + 2) $stop;

      rtim1 = 2;
      rtim2 = 2.6;
      # (rtim1 + rtim2);  // Rounds up
      if ($time != 1 + 2 + 5) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
