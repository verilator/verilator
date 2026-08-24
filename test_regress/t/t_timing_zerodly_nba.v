// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A non-blocking assignment made by a process that was resumed after a #0
// must take effect in that same time slot: IEEE 1800-2023 4.5 puts the NBA
// region after the Inactive region of one time slot, not of the next one.

module t;

   logic [3:0] x = 4'h0;
   logic [3:0] y;
   int         z;

   assign y = x;
   assign z = (x == 4'h4) ? 40 : (x == 4'h7) ? 70 : -1;

   initial begin
      // The #0 is what puts the assignment below in the Inactive region
      #0;
      x <= 4'h4;
      #1;
      if (x !== 4'h4) $stop;
      if (y !== 4'h4) $stop;
      if (z !== 40) $stop;

      // And again, to show it is not a one-off at time zero
      #0;
      x <= 4'h7;
      #1;
      if (y !== 4'h7) $stop;
      if (z !== 70) $stop;

      // Without a #0 the same assignment has always worked
      x <= 4'h4;
      #1;
      if (y !== 4'h4) $stop;
      if (z !== 40) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
