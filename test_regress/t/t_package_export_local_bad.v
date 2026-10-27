// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package P1;
  integer x = 123;
endpackage

package P2;
  import P1::*;
  integer x = 456;
  export P1::x;  // <--- Error: conflicts with local declaration
endpackage

package P3;
  import P1::*;
  export P1::x;  // <--- Error: conflicts with local declaration, even if declared after
  integer x = 456;
endpackage

module t;
endmodule
