// DESCRIPTION: Test for IEEE 1800-2023 6.22.2 - valid array assignments with matching state types
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   // 2-state arrays - assignment should work
   bit [7:0] arr_2state_a [3:0];
   bit [7:0] arr_2state_b [3:0];

   // 4-state arrays - assignment should work
   logic [7:0] arr_4state_a [3:0];
   logic [7:0] arr_4state_b [3:0];

   initial begin
      // Initialize
      arr_2state_a[0] = 8'h10;
      arr_2state_a[1] = 8'h20;
      arr_2state_a[2] = 8'h30;
      arr_2state_a[3] = 8'h40;

      arr_4state_a[0] = 8'hA0;
      arr_4state_a[1] = 8'hB0;
      arr_4state_a[2] = 8'hC0;
      arr_4state_a[3] = 8'hD0;

      // Valid assignments: same state types
      arr_2state_b = arr_2state_a;  // 2-state to 2-state: OK
      arr_4state_b = arr_4state_a;  // 4-state to 4-state: OK

      // Verify
      if (arr_2state_b[0] !== 8'h10) $stop;
      if (arr_2state_b[3] !== 8'h40) $stop;
      if (arr_4state_b[0] !== 8'hA0) $stop;
      if (arr_4state_b[3] !== 8'hD0) $stop;

      $write("*-* All Coverage *-*\n");
      $finish;
   end
endmodule
