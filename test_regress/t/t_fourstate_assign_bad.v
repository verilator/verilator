// DESCRIPTION: Test for IEEE 1800-2023 6.22.2 - 4-state to 2-state type equivalence
// This should produce a type error because bit and logic are not equivalent types
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  // IEEE 6.22.2: Packed arrays are equivalent if they contain the same number
  // of total bits, are either all 2-state or all 4-state, and are either all
  // signed or all unsigned.

  // 2-state array
  bit [7:0] arr_2state[3:0];

  // 4-state array (should not be assignment compatible for unpacked arrays)
  logic [7:0] arr_4state[3:0];

  initial begin
    // Per IEEE 7.6: For unpacked arrays to be assignment compatible,
    // the element types shall be equivalent.
    // bit[7:0] and logic[7:0] are NOT equivalent (one is 2-state, one is 4-state)
    arr_2state = arr_4state;
    $write("*-* All Coverage *-*\n");
    $stop;
  end
endmodule
